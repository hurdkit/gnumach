/*
 * Copyright (c) 2010, 2011, 2016, 2019 Free Software Foundation, Inc.
 *
 * Permission to use, copy, modify and distribute this software and its
 * documentation is hereby granted, provided that both the copyright
 * notice and this permission notice appear in all copies of the
 * software, derivative works or modified versions, and any portions
 * thereof, and that both notices appear in supporting documentation.
 *
 * THE FREE SOFTWARE FOUNDATIONALLOWS FREE USE OF THIS SOFTWARE IN ITS "AS IS"
 * CONDITION.  THE FREE SOFTWARE FOUNDATION DISCLAIMS ANY LIABILITY OF ANY KIND
 * FOR ANY DAMAGES WHATSOEVER RESULTING FROM THE USE OF THIS SOFTWARE.
 */

#include <kern/assert.h>
#include <device/intr.h>
#include <device/device_types.h>
#include <device/device_port.h>
#include <device/notify.h>
#include <kern/printf.h>
#include <machine/spl.h>
#include <machine/irq.h>
#include <ipc/ipc_space.h>
#include <device/irq_status.h>

/*ARGSUSED*/
io_return_t irqgetstat(
  dev_t        dev,
  dev_flavor_t flavor,
  dev_status_t data,			/* pointer to OUT array */
  mach_msg_type_number_t *count)	/* OUT */
{
  io_return_t result = D_SUCCESS;

  switch (flavor)
    {
#ifndef MACH_XEN
      case IRQGETPICMODE:
        *data = pic_mode;
        *count = 1;
        break;
#endif
      default:
        result = D_INVALID_OPERATION;
        break;
    }

  return (result);
}

#ifndef MACH_XEN

def_simple_lock_irq_data(static, intr_lock)

/* An entry whose notifications were delivered but left unacked for
 * this many consecutive quiescent wakes of intr_thread (~1 s apart
 * when idle) has its unacked counts dropped, exactly like the
 * dead-entry reap does, so that a lost or never-processed
 * notification cannot mask a shared irq line forever.  */
#define STALE_UNACKED_SWEEPS 5

queue_head_t main_intr_queue;

/* True while any entry may have unacknowledged deliveries, set when a
 * delivery is queued, cleared by the recovery sweep once no entry has
 * unacked counts left.  Gates the once-per-wake sweep so an idle queue
 * costs one branch instead of a full walk.  */
static boolean_t intr_recover_pending = FALSE;
static boolean_t deliver_intr (int id, ipc_port_t dst_port);

#ifndef LINUX_DEV
#define SA_SHIRQ 0x04000000

struct intr_list {
  user_intr_t *user_intr;
  unsigned long flags;
  struct intr_list *next;
};
static struct intr_list *user_intr_handlers[NINTR];
#endif

static user_intr_t *
search_intr (struct irqdev *dev, ipc_port_t dst_port)
{
  user_intr_t *e;
  queue_iterate (dev->intr_queue, e, user_intr_t *, chain)
    {
      if (e->dst_port == dst_port)
	return e;
    }
  return NULL;
}


/*
 * Interrupt handling logic:
 * PCI interrupts are raised on master processor only.
 *
 * interrupt.S raises spl (thus IF cleared)
 * For edge triggered interrupts (to ensure none are missed):
 *   - interrupt.S EOI
 *   - interrupt.S calls the handler
 * For level triggered interrupts (to prevent stacking):
 *   - interrupt.S calls the handler
 *   - interrupt.S EOI
 *
 * For pure in-kernel handlers, they do whatever they want with IF cleared.
 * When a userland handler is registered, queue_intr masks the irq.
 * interrupt.S lowers spl with splx_cli, thus IF still cleared
 * iret, that also sets IF
 *
 * later on, (irq_acknowledge), userland acks the IRQ, that unmasks the irq
 */
kern_return_t
irq_acknowledge (ipc_port_t receive_port)
{
  user_intr_t *e;
  kern_return_t ret = 0;

  spl_t s = simple_lock_irq(&intr_lock);
  e = search_intr (&irqtab, receive_port);

  if (!e)
    {
      printf("didn't find user intr for interrupt !?\n");
      ret = KERN_INVALID_ARGUMENT;
    }
  else
    {
      if (!e->n_unacked)
        ret = D_INVALID_OPERATION;
      else
        {
          e->n_unacked--;
          e->stale = 0;
        }
    }
  simple_unlock_irq(s, &intr_lock);

  if (ret)
    return ret;

  __enable_irq (irqtab.irq[e->id]);

  return D_SUCCESS;
}

/* This function can only be used in the interrupt handler. */
static void
queue_intr (struct irqdev *dev, int id, user_intr_t *e)
{
  /* Until userland has handled the IRQ in the driver, we have to keep it
   * disabled. Level-triggered interrupts would keep raising otherwise. */
  __disable_irq (dev->irq[id]);

#ifdef LINUX_DEV /* user_irq_handler does its own locking */
  spl_t s = simple_lock_irq(&intr_lock);
#endif
  e->n_unacked++;
  e->stale = 0;
  e->interrupts++;
  dev->tot_num_intr++;
  intr_recover_pending = TRUE;
#ifdef LINUX_DEV
  simple_unlock_irq(s, &intr_lock);
#endif

  thread_wakeup ((event_t) &intr_thread);
}

int
deliver_user_intr (struct irqdev *dev, int id, user_intr_t *e)
{
  /* The reference of the port was increased
   * when the port was installed.  If the reference is 1, it means
   * the port was deallocated and we should clean after it. */
  if (!e->dst_port || e->dst_port->ip_references == 1)
    {
      thread_wakeup ((event_t) &intr_thread);
      return 0;
    }
  else
    {
      queue_intr (dev, id, e);
      return 1;
    }
}

/* insert an interrupt entry in the queue.
 * This entry exists in the queue until
 * the corresponding interrupt port is removed.*/
user_intr_t *
insert_intr_entry (struct irqdev *dev, int id, ipc_port_t dst_port)
{
  user_intr_t *e, *new, *ret;
  int free = 0;

  new = (user_intr_t *) kalloc (sizeof (*new));
  if (new == NULL)
    return NULL;

  /* check whether the intr entry has been in the queue. */
  spl_t s = simple_lock_irq(&intr_lock);
  e = search_intr (dev, dst_port);
  if (e)
    {
      printf ("the interrupt entry for irq[%d] and port %p has already been inserted\n", id, dst_port);
      free = 1;
      ret = NULL;
      goto out;
    }
  printf("irq handler [%d]: new delivery port %p entry %p for %s\n", id, dst_port, new, current_task()->name);
  ret = new;
  new->id = id;
  new->dst_port = dst_port;
  new->interrupts = 0;
  new->n_unacked = 0;
  new->stale = 0;

  queue_enter (dev->intr_queue, new, user_intr_t *, chain);
out:
  simple_unlock_irq(s, &intr_lock);
  if (free)
    kfree ((vm_offset_t) new, sizeof (*new));
  return ret;
}

#ifndef LINUX_DEV

static void
user_irq_handler (int id)
{
  struct intr_list *handler;
  struct intr_list **prev = &user_intr_handlers[id];
  user_intr_t *e;
  spl_t s;

  s = simple_lock_irq(&intr_lock);

  for (handler = *prev; handler; handler = handler->next)
    {
      e = handler->user_intr;
      if (!deliver_user_intr(&irqtab, id, e))
        {
          /* We failed to deliver this interrupt, remove handler from list */
	  *prev = handler->next;
        }
      prev = &handler->next;
    }
  simple_unlock_irq(s, &intr_lock);
}

int
install_user_intr_handler (struct irqdev *dev, int id, unsigned long flags,
			  user_intr_t *user_intr)
{
  unsigned int irq = dev->irq[id];
  struct intr_list **head = &user_intr_handlers[id];
  struct intr_list *new, *old = *head;
  spl_t s;

  flags |= SA_SHIRQ;

  assert (irq < NINTR);

  /* Don't allow overriding hardclock/kdintr etc */
  if ((ivect[irq] != user_irq_handler) && (ivect[irq] != intnull))
    {
      printf("You can't have this interrupt %d:%d\n", id, irq);
      return D_ALREADY_OPEN;
    }

  if (old)
    {
      if (!(old->flags & flags & SA_SHIRQ))
        {
          printf ("Cannot share irq\n");
          return D_ALREADY_OPEN;
        }
    }

  new = (struct intr_list *)kalloc (sizeof (struct intr_list));
  new->user_intr = user_intr;
  new->flags = flags;

  s = simple_lock_irq(&intr_lock);
  new->next = *head;
  *head = new;
  ivect[irq] = user_irq_handler;
  iunit[irq] = (int)irq;
  unmask_irq (irq);
  simple_unlock_irq(s, &intr_lock);

  return D_SUCCESS;
}
#endif

void
intr_thread (void)
{
  user_intr_t *e;
  int id;
  ipc_port_t dst_port;

  current_thread()->vm_privilege = 1;
  queue_init (&main_intr_queue);

  for (;;)
    {
      assert_wait ((event_t) &intr_thread, FALSE);
      /* Make sure we wake up from times to times to check for aborted processes */
      thread_set_timeout (hz);
      spl_t s = simple_lock_irq(&intr_lock);

      /* Now check for interrupts */
      int del;
      do
	{
	  del = 0;

	  queue_iterate (&main_intr_queue, e, user_intr_t *, chain)
	    {
	      /* The reference of the port was increased
               * when the port was installed.  If the reference is 1, it means
               * the port was deallocated and we should clean after it. */
	      if (e->dst_port->ip_references == 1)
		{
		  clear_wait (current_thread (), 0, 0);
		  del = 1;
		  break;
		}

	      if (e->interrupts)
		{
		  clear_wait (current_thread (), 0, 0);
		  id = e->id;
		  dst_port = e->dst_port;
		  e->interrupts--;
		  irqtab.tot_num_intr--;

		  simple_unlock_irq(s, &intr_lock);
		  if (!deliver_intr (id, dst_port))
		    {
		      /* The send failed (e.g. ikm_alloc under kmsg pool
		       * pressure).  Restore the counts so the next wake retries
		       * the delivery: a lost send would otherwise strand the
		       * per-irq nesting counter and mask a shared irq line
		       * forever.  */
		      s = simple_lock_irq(&intr_lock);
		      e->interrupts++;
		      irqtab.tot_num_intr++;
		      simple_unlock_irq(s, &intr_lock);
		    }
		  s = simple_lock_irq(&intr_lock);
		}
	    }

	  /* remove the entry without dest port from the queue and free it. */
	  if (del)
	    {
	      /*
	       * We clear unacked irqs now, so the Linux handling can trigger,
	       * and we will cleanup later after the Linux handler is cleared.
	       */
	      assert (!queue_empty (&main_intr_queue));
	      queue_remove (&main_intr_queue, e, user_intr_t *, chain);

	      printf ("irq handler [%d]: release a dead delivery port %p entry %p\n", e->id, e->dst_port, e);
	      ipc_port_release (e->dst_port);
	      e->dst_port = MACH_PORT_NULL;

	      if (e->n_unacked)
		printf("irq handler [%d]: still %d unacked irqs in entry %p\n", e->id, e->n_unacked, e);
	      while (e->n_unacked)
	      {
		__enable_irq (irqtab.irq[e->id]);
		e->n_unacked--;
	      }

	      /* Account for all interrupts that could not be delivered */
	      irqtab.tot_num_intr -= e->interrupts;
	      e->interrupts = 0;

#ifndef LINUX_DEV
	      /* Remove the handler from the per-irq list: with the port
	       * released and the entry dequeued nothing else references
	       * the entry, so both can be freed.  */
	      {
		struct intr_list **prev = &user_intr_handlers[e->id];
		while (*prev)
		  {
		    if ((*prev)->user_intr == e)
		      {
			struct intr_list *l = *prev;
			*prev = l->next;
			simple_unlock_irq(s, &intr_lock);
			kfree ((vm_offset_t) l, sizeof (*l));
			s = simple_lock_irq(&intr_lock);
			break;
		      }
		    prev = &(*prev)->next;
		  }
	      }
	      simple_unlock_irq(s, &intr_lock);
	      kfree ((vm_offset_t) e, sizeof (*e));
	      s = simple_lock_irq(&intr_lock);
#else
	      /* With the Linux irq glue we don't control the action list:
	       * the glue unlinks this entry's action when the next
	       * interrupt finds its port gone, so the entry has to stay
	       * allocated until then.  */
#endif
	    }
	}
      while (del || irqtab.tot_num_intr);

      /* Recovery sweep, once per wake, but only while unacknowledged
       * deliveries may exist: queue_intr raises intr_recover_pending,
       * and the sweep clears it once no entry has unacked counts left,
       * so a fully acked queue costs one branch instead of a walk.
       * Notifications delivered but
       * never acked keep the per-irq nesting counter (i386/i386/irq.c)
       * above zero, which masks a shared irq line for every driver on
       * it.  Alive-but-stuck entries are never reaped, so drop their
       * unacked counts exactly like the dead-entry reap does, after a
       * grace period; a level line still asserted by the device then
       * refires and notifies the driver afresh.  A late ack from a
       * slow-but-alive driver lands on the n_unacked == 0 guard and is
       * rejected.  */
      if (intr_recover_pending)
	{
	  boolean_t outstanding = FALSE;

	  queue_iterate (&main_intr_queue, e, user_intr_t *, chain)
	    {
	      if (!e->dst_port || e->dst_port->ip_references == 1)
		continue;

	      if (e->n_unacked)
		{
		  outstanding = TRUE;
		  if (e->interrupts)
		    /* A fresh batch is queued for delivery, the grace
		     * count restarts when it has been sent.  */
		    e->stale = 0;
		  else
		    {
		      e->stale++;
		      if (e->stale >= STALE_UNACKED_SWEEPS)
			{
			  printf ("irq handler [%d]: entry %p left %d irqs unacked,"
				  " dropping count to unmask the line\n",
				  e->id, e, e->n_unacked);
			  while (e->n_unacked)
			    {
			      __enable_irq (irqtab.irq[e->id]);
			      e->n_unacked--;
			    }
			  e->stale = 0;
			}
		    }
		}
	      else
		e->stale = 0;
	    }
	  if (!outstanding)
	    intr_recover_pending = FALSE;
	}

      simple_unlock_irq(s, &intr_lock);
      thread_block (NULL);
    }
}

static boolean_t
deliver_intr (int id, ipc_port_t dst_port)
{
  ipc_kmsg_t kmsg;
  device_intr_notification_t *n;
  mach_port_t dest = (mach_port_t) dst_port;

  if (dest == MACH_PORT_NULL)
    return FALSE;

  kmsg = ikm_alloc(sizeof *n);
  if (kmsg == IKM_NULL)
    return FALSE;

  ikm_init(kmsg, sizeof *n);
  n = (device_intr_notification_t *) &kmsg->ikm_header;

  mach_msg_header_t *m = &n->intr_header;
  mach_msg_type_t *t = &n->intr_type;

  m->msgh_bits = MACH_MSGH_BITS(MACH_MSG_TYPE_PORT_SEND, 0);
  m->msgh_size = sizeof *n;
  m->msgh_seqno = DEVICE_NOTIFY_MSGH_SEQNO;
  m->msgh_local_port = MACH_PORT_NULL;
  m->msgh_remote_port = MACH_PORT_NULL;
  m->msgh_id = DEVICE_INTR_NOTIFY;

  t->msgt_name = MACH_MSG_TYPE_INTEGER_32;
  t->msgt_size = 32;
  t->msgt_number = 1;
  t->msgt_inline = TRUE;
  t->msgt_longform = FALSE;
  t->msgt_deallocate = FALSE;
  t->msgt_unused = 0;

  n->intr_header.msgh_remote_port = dest;
  n->id = id;

  /* For an inactive port ipc_port_copy_send returns IP_DEAD without
   * taking a reference, while the dead-port branch of
   * ipc_mqueue_send_always releases one: sending would drop a
   * reference that was never taken.  Drop the notification instead;
   * the dead-entry reap in intr_thread reclaims the entry.  */
  if (ipc_port_copy_send (dst_port) == IP_DEAD)
    {
      ikm_free (kmsg);
      return TRUE;
    }

  ipc_mqueue_send_always(kmsg);

  return TRUE;
}

#endif	/* MACH_XEN */
