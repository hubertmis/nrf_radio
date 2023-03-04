//! Deffered job items executor
//!
//! Tasklets are small job items (single function) which can be executed later. They are mainly
//! used by timing critical code to schedule execution of less critical functions. Typically ISRs
//! can schedule functions to be executed from a thread context after an ISR is finished.
//!
//! Tasklets implementation utilizes [`LinkedList`](crate::utils::linked_list::LinkedList) to store
//! job items heapless, with unlimited number of entries. The users of the tasklet module are
//! responsible to maintain memory required to manage given tasklet (keep `Tasklet` structure alive
//! as long as it might be in a queue).
//!
//! The user of given tasklet queue is responsible to run given queue periodically from a thread
//! context. The period of the queue running results is the source of tasklets latency.
//!
//! # Examples
//!
//! ```no_run
//! # #[macro_use] extern crate nrf_radio;
//! # missing_test_fns!();
//! # fn main() {
//! use nrf_radio::utils::tasklet::{Context, Tasklet, TaskletListItem, TaskletQueue};
//!
//! static mut TASKLET_EXECUTED: bool = false;
//!
//! let mut tasklet = Tasklet::new(tasklet_function, &tasklet_context);
//! static tasklet_context: &str = "context data";
//!
//! let mut queue = TaskletQueue::new();
//! queue.push(&mut tasklet);
//! queue.run();
//!
//! // Safety: TASKLET_EXECUTED is accessed by a tasklet only during queue.run(). Now it's safe
//! //         to access it from here.
//! assert!(unsafe {TASKLET_EXECUTED});
//!
//! fn tasklet_function(_list_item: &mut TaskletListItem, context: Context) {
//!   let string = context
//!       .downcast_ref::<&str>()
//!       .unwrap();
//!   assert_eq!(string, &"context data");
//!
//!   // Safety: the tasklet user expect this tasklet to access TASKLET_EXECUTED. It's safe to
//!   //         do so from this context
//!   unsafe {TASKLET_EXECUTED = true};
//! }
//! # }
//! ```

use crate::crit_sect;
use crate::mutex::Mutex;
use crate::utils::linked_list::{LinkedList, ListItem, ListItemToken};
use core::any::Any;
use core::ops::{Deref, DerefMut};

/// [`ListItem`](crate::utils::linked_list::ListItem) storing a tasklet
pub type TaskletListItem<'a> = ListItem<'a, TaskletData<'a>>;
/// Reference to anything. This reference is blindly passed to the tasklet function
pub type Context = &'static (dyn Any + Send + Sync);
/// Type of function usable by tasklet
///
/// This function takes two parameters:
/// * exclusive reference to the list item associated with this tasklet - it allows to use the
///   same tasklet again
/// * context selected by user when scheduling the tasklet
pub type TaskletFn<'queue> = fn(&'queue mut TaskletListItem<'queue>, Context);

/// Queue of tasklets
pub struct TaskletQueue<'queue>(Mutex<LinkedList<'queue, TaskletData<'queue>>>);

impl<'queue> TaskletQueue<'queue> {
    /// Create an empty queue for running tasklets
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::utils::tasklet::TaskletQueue;
    ///
    /// let queue = TaskletQueue::new();
    /// ```
    pub fn new() -> Self {
        Self(Mutex::new(LinkedList::new()))
    }

    /// Add a new tasklet to the queue
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::{Tasklet, TaskletQueue, TaskletListItem, Context};
    ///
    /// let queue = TaskletQueue::new();
    /// let mut tasklet = Tasklet::new(callback, &None::<bool>);
    ///
    /// queue.push(&mut tasklet);
    ///
    /// fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
    ///     // Deferred job
    /// }
    /// # }
    /// ```
    pub fn push(
        &self,
        tasklet: &'queue mut ListItem<'queue, TaskletData<'queue>>,
    ) -> ListItemToken<'queue, TaskletData<'queue>> {
        crit_sect::locked(|cs| self.0.borrow_mut(cs).push(tasklet))
    }

    /// Get a tasklet from the head of the queue
    fn pop(&self) -> Option<&'queue mut ListItem<'queue, TaskletData<'queue>>> {
        crit_sect::locked(|cs| self.0.borrow_mut(cs).pop())
    }

    /// Get a mutable reference to a tasklet using a linked list token
    ///
    /// The token is obtained when the tasklet is pushed to the queue. This token can be used to
    /// get back the mutable reference to the tasklet.
    ///
    /// # Safety
    ///
    /// Call this function only when you know that the tasklet represented by this token was already
    /// removed from the queue (it's callback has already finished) and the reference to the
    /// tasklet was dropped (the reference to the tasklet available in the callback was dropped).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::{Tasklet, TaskletQueue, TaskletListItem, Context};
    ///
    /// let queue = TaskletQueue::new();
    /// let mut tasklet = Tasklet::new(callback, &None::<bool>);
    ///
    /// let token = queue.push(&mut tasklet);
    ///
    /// queue.run();
    ///
    /// // Safety: The queue containing the tasklet was run, so the callback has finished. And the
    /// //         callback functions drops _tasklet_ref reference to the tasklet
    /// unsafe {
    ///   let tasklet_ref: &mut TaskletListItem = queue.get_unchecked(token);
    ///   // Tasklet be modified now, or added again to the queue
    /// }
    ///
    /// fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
    ///     // Deferred job
    ///
    ///     // _tasklet_ref is dropped here
    /// }
    /// # }
    /// ```
    pub unsafe fn get_unchecked(
        &self,
        token: ListItemToken<'queue, TaskletData<'queue>>,
    ) -> &'queue mut ListItem<'queue, TaskletData<'queue>> {
        crit_sect::locked(|cs| self.0.borrow_mut(cs).get_unchecked(token))
    }

    /// Run all tasklets scheduled in this queue
    ///
    /// Tasklets are executed in any order
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::TaskletQueue;
    ///
    /// let mut queue = TaskletQueue::new();
    /// queue.run();
    /// # }
    /// ```
    pub fn run(&self) {
        while let Some(tasklet) = self.pop() {
            tasklet.run();
        }
    }
}

impl Default for TaskletQueue<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Data needed to schedule a tasklet
///
/// This structure is handled by the [`Tasklet`] structure. It is considered internal detail of the
/// implementation.
#[derive(Debug)]
pub struct TaskletData<'a> {
    function: TaskletFn<'a>,
    context: Context,
}

/// Actual tasklet which can be queued for defered execution
pub struct Tasklet<'tasklet>(TaskletListItem<'tasklet>);

impl<'tasklet> Tasklet<'tasklet> {
    /// Create new tasklet with a function and associated context
    ///
    /// A tasklet must be added to a [queue](TaskletQueue) to be executed.
    /// A tasklet must be mutable to be added to a queue.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::{Context, Tasklet, TaskletListItem};
    ///
    /// let mut tasklet = Tasklet::new(tasklet_function, &None::<usize>);
    ///
    /// fn tasklet_function(_list_item: &mut TaskletListItem, _context: Context) {
    ///   // Run defered action
    /// }
    /// # }
    /// ```
    // TODO: This function should be const. Is it possible to make it?
    pub fn new(function: TaskletFn<'tasklet>, context: Context) -> Self {
        Self(ListItem::new(TaskletData { function, context }))
    }

    /// Convert reference to this object to internal
    /// [`ListItem`](crate::utils::linked_list::ListItem)
    ///
    /// This conversion is helpful to store mutable reference to a tasklet and then refresh it
    /// after the callback is executed and the tasklet borrowed by the queue is returned.
    ///
    /// # Examples
    ///
    /// The tasklet reference may be stored in a static variable so that it can be updated from the
    /// defered function
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # #[macro_use] extern crate lazy_mut;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::{Context, Tasklet, TaskletListItem, TaskletQueue};
    ///
    /// lazy_mut! {
    ///   // Define a tasklet with its function and empty context
    ///   static mut TASKLET: Tasklet<'static> = Tasklet::new(callback, &None::<usize>);
    /// };
    /// // Reference to a tasklet is used to borrow the tasklet to the queue and get it back when
    /// // it is executed
    /// static mut TASKLET_REF: Option<&mut TaskletListItem> = None;
    ///
    /// // Initialize static variables
    /// unsafe { TASKLET.init() };
    /// unsafe { TASKLET_REF = Some(TASKLET.as_mut_list_item()) };
    ///
    /// // Create a tasklet queue
    /// let mut queue = TaskletQueue::new();
    ///
    /// for i in 0..100 {
    ///   // The queue borrows the tasklet when it is added to the queue
    ///   // Ignore token, because it's not needed in this sequence
    ///   queue.push(unsafe { TASKLET_REF.take() }.unwrap());
    ///   // While tasklet is borrowed, I don't have reference to it
    ///   assert!(unsafe { TASKLET_REF.is_none() });
    ///   // Run queue. The callback function retrieves the borrowed reference after the tasklet is
    ///   // executed
    ///   queue.run();
    ///   // Returned reference is restored as TASKLET_REF
    ///   assert!(unsafe { TASKLET_REF.is_some() });
    /// }
    ///
    /// fn callback(tasklet_ref: &'static mut TaskletListItem, _context: Context) {
    ///     // Run defered action
    ///
    ///     // The borrowed tasklet is returned now and I store it to use it again soon
    ///     unsafe { TASKLET_REF = Some(tasklet_ref) };
    /// }
    /// # }
    /// ```
    ///
    /// Alternatively unsafe
    /// [`get_unchecked()`](crate::utils::linked_list::LinkedList::get_unchecked) can be used to
    /// retrieve the tasklet reference after the tasklet is executed.
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::utils::tasklet::{Context, Tasklet, TaskletListItem, TaskletQueue};
    ///
    /// let mut tasklet = Tasklet::new(callback, &None::<bool>);
    /// let mut tasklet_ref = tasklet.as_mut_list_item();
    ///
    /// let mut queue = TaskletQueue::new();
    ///
    /// for i in 0..100 {
    ///     // The queue borrows the tasklet and gives a token
    ///     let token = queue.push(tasklet_ref);
    ///     queue.run();
    ///
    ///     // Safety: after the queue was executed, the tasklets are removed from the queue and
    ///     //         references to tasklets are passed to callbacks. My callback implementation
    ///     //         drops `_tasklet_ref`. The tasklet is removed from the queue and reference is
    ///     //         dropped. It means that the tasklet reference can be safely retrieved using
    ///     //         the token.
    ///     tasklet_ref = unsafe { queue.get_unchecked(token) };
    /// }
    ///
    /// fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
    ///     // Run defered action
    /// }
    /// # }
    /// ```
    pub fn as_mut_list_item(&mut self) -> &mut TaskletListItem<'tasklet> {
        self
    }
}

impl<'tasklet> Deref for Tasklet<'tasklet> {
    type Target = TaskletListItem<'tasklet>;

    fn deref(&self) -> &<Self as Deref>::Target {
        &self.0
    }
}

impl<'tasklet> DerefMut for Tasklet<'tasklet> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'item> TaskletListItem<'item> {
    fn run(&'item mut self) {
        (self.function)(self, self.context);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run_empty_tasklet_queue() {
        let queue = TaskletQueue::new();
        queue.run();
    }

    #[test]
    fn test_run_tasklet_queue_with_single_entry() {
        static mut CALLED: bool = false;
        fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
            unsafe { CALLED = true };
        }

        let queue = TaskletQueue::new();
        let mut tasklet = Tasklet::new(callback, &None::<bool>);
        queue.push(&mut tasklet);

        assert_eq!(unsafe { CALLED }, false);
        queue.run();
        assert_eq!(unsafe { CALLED }, true);
    }

    #[test]
    fn test_run_tasklet_queue_with_single_entry_multiple_times() {
        lazy_mut! {
            static mut TASKLET: Tasklet<'static> = Tasklet::new(callback, &None::<bool>);
        };
        static mut CALL_CNT: u32 = 0;
        static mut TASKLET_REF: Option<&mut TaskletListItem> = None;

        fn callback(tasklet_ref: &'static mut TaskletListItem, _context: Context) {
            unsafe { CALL_CNT += 1 };
            unsafe { TASKLET_REF = Some(tasklet_ref) };
        }

        let queue = TaskletQueue::new();
        unsafe { TASKLET.init() };
        unsafe { TASKLET_REF = Some(TASKLET.as_mut_list_item()) };

        for i in 0..100 {
            queue.push(unsafe { TASKLET_REF.take() }.unwrap());
            assert_eq!(unsafe { CALL_CNT }, i);
            queue.run();
            assert_eq!(unsafe { CALL_CNT }, i + 1);
        }
    }

    #[test]
    fn test_run_tasklet_queue_with_single_entry_multiple_times_using_token() {
        static mut CALL_CNT: u32 = 0;

        fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
            unsafe { CALL_CNT += 1 };
        }

        let queue = TaskletQueue::new();
        let mut tasklet = Tasklet::new(callback, &None::<bool>);
        let mut tasklet_ref = tasklet.as_mut_list_item();

        for i in 0..100 {
            let token = queue.push(tasklet_ref);
            assert_eq!(unsafe { CALL_CNT }, i);
            queue.run();
            assert_eq!(unsafe { CALL_CNT }, i + 1);
            tasklet_ref = unsafe { queue.get_unchecked(token) };
        }
    }

    #[test]
    fn test_run_tasklet_queue_with_multiple_entries() {
        use core::cell::RefCell;

        struct SyncWrapper<T> {
            inner: T,
        }

        impl<T> SyncWrapper<T> {
            pub const fn new(value: T) -> SyncWrapper<T> {
                Self { inner: value }
            }

            pub fn borrow(&self) -> &T {
                &self.inner
            }
        }

        unsafe impl<T> Sync for SyncWrapper<T> where T: Send {}

        const N: usize = 100;
        const NOT_CALLED: SyncWrapper<RefCell<bool>> = SyncWrapper::new(RefCell::new(false));

        static mut CALLED: [SyncWrapper<RefCell<bool>>; N] = [NOT_CALLED; N];
        fn callback(_tasklet_ref: &mut TaskletListItem, context: Context) {
            let mut called = context
                .downcast_ref::<SyncWrapper<RefCell<bool>>>()
                .unwrap()
                .borrow()
                .borrow_mut();
            *called = true;
        }

        let queue = TaskletQueue::new();
        let mut tasklets = Vec::new();

        for i in 0..N {
            tasklets.push(Tasklet::new(callback, unsafe { &CALLED[i] }));
        }

        for tasklet in tasklets.iter_mut() {
            queue.push(tasklet);
        }

        for i in 0..N {
            assert_eq!(unsafe { *(CALLED[i].borrow().borrow()) }, false);
        }
        queue.run();
        for i in 0..N {
            assert_eq!(unsafe { *(CALLED[i].borrow().borrow()) }, true);
        }
    }

    #[test]
    fn test_tasklet_is_called_once() {
        static mut CALL_CNT: u32 = 0;
        fn callback(_tasklet_ref: &mut TaskletListItem, _context: Context) {
            unsafe { CALL_CNT += 1 };
        }

        let queue = TaskletQueue::new();
        let mut tasklet = Tasklet::new(callback, &None::<bool>);
        queue.push(&mut tasklet);

        assert_eq!(unsafe { CALL_CNT }, 0);
        for _ in 0..100 {
            queue.run();
        }
        assert_eq!(unsafe { CALL_CNT }, 1);
    }
}
