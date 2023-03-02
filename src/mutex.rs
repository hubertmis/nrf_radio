//! Mutex ensuring that access to variables accessible from radio IRQs is mutually exclusive.
//!
//! This mutex requires proof of disabled radio IRQs provided by the `CriticalSection`'s lock

use crate::crit_sect::CriticalSection;

/// Wraps variable which is accessible from radio IRQ
pub struct Mutex<T> {
    inner: T,
}

impl<T> Mutex<T> {
    /// Creates new wrapper for a variable accessible from radio IRQ
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::mutex::Mutex;
    ///
    /// static mut ISR_CALLED: Mutex<bool> = Mutex::new(false);
    /// ```
    pub const fn new(value: T) -> Mutex<T> {
        Self { inner: value }
    }

    /// Borrows Mutex's internal variable with mutually exclusive access
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use core::cell::RefCell;
    /// use nrf_radio::crit_sect;
    /// use nrf_radio::mutex::Mutex;
    ///
    /// static ISR_CALLED: Mutex<RefCell<bool>> = Mutex::new(RefCell::new(false));
    ///
    /// crit_sect::locked(|cs_token| {
    ///   *ISR_CALLED.borrow(cs_token).borrow_mut() = true;
    /// });
    /// # }
    /// ```
    pub fn borrow<'cs>(&'cs self, _cs: &'cs CriticalSection) -> &'cs T {
        &self.inner
    }
}

// Safety: Mutex is Sync assumming contained type is Send and the CriticalSection module prevents
// concurrent access to Mutex from multiple contexts. This assumption is verified run-time if
// RefCell is used inside the mutex
unsafe impl<T> Sync for Mutex<T> where T: Send {}
