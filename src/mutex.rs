//! Mutex ensuring that access to variables accessible from radio IRQs is mutually exclusive.
//!
//! This mutex requires proof of disabled radio IRQs provided by the `CriticalSection`'s lock

use crate::crit_sect::CriticalSection;
use core::cell::{Ref, RefCell, RefMut};

// TODO create Mutexes for specific IRQs, or lists of IRQs like radio + timer
/// Wraps variable which is accessible from an IRQ
pub struct Mutex<T>(RefCell<T>);

impl<T> Mutex<T> {
    /// Creates new wrapper for a variable accessible from an IRQ
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::mutex::Mutex;
    ///
    /// static mut ISR_CALLED: Mutex<bool> = Mutex::new(false);
    /// ```
    pub const fn new(value: T) -> Mutex<T> {
        Self(RefCell::new(value))
    }

    /// Borrows Mutex's internal variable with mutually exclusive access
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::crit_sect;
    /// use nrf_radio::mutex::Mutex;
    ///
    /// static ISR_READ_ONLY_DATA: Mutex<u32> = Mutex::new(15);
    ///
    /// crit_sect::locked(|cs_token| {
    ///   assert_eq!(*ISR_READ_ONLY_DATA.borrow(cs_token), 15);
    /// });
    /// # }
    /// ```
    pub fn borrow<'cs>(&'cs self, _cs: &'cs CriticalSection) -> Ref<'cs, T> {
        self.0.borrow()
    }

    /// Mutably borrows Mutex's internal variable with mutually exclusive access
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::crit_sect;
    /// use nrf_radio::mutex::Mutex;
    ///
    /// static ISR_CALLED: Mutex<bool> = Mutex::new(false);
    ///
    /// crit_sect::locked(|cs_token| {
    ///   *ISR_CALLED.borrow_mut(cs_token) = true;
    /// });
    /// # }
    /// ```
    pub fn borrow_mut<'cs>(&'cs self, _cs: &'cs CriticalSection) -> RefMut<'cs, T> {
        self.0.borrow_mut()
    }
}

// Safety: Mutex is Sync assumming contained type is Send and the CriticalSection module prevents
// concurrent access to Mutex from multiple contexts. This assumption is verified run-time by
// RefCell used inside the mutex
// TODO: Instead of using RefCell maybe some other mechanism like AtomicBool to check if mutex is
// being borrowed simultaneously from multiple contexts? Or checking run-time thread/handler mode
// and finding handler mode if given IRQ is being blocked by mutex
unsafe impl<T> Sync for Mutex<T> where T: Send {}
