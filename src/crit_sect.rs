//! Critical section implementation allowing safe access to variables accessible from both threads
//! and ISRs.
//!
//! Variables accessible from ISRs usually are defined as static. Access to them from threads
//! should be from critical sections which disable at least those IRQs which handlers access these
//! variables. If such IRQs are not disabled, there may be data races.
//!
//! One other way of avoiding data races is using atomic variables, but it is considered a special
//! case and handled in other ways.

// TODO: Implement own mutex abstraction instead of relying on cortex_m blocking IRQs
//       It should block only IRQs which can enter this function

/// Critical Section token
///
/// Whoever owns the critical section token can safely access variables guarded by such critical
/// section.
pub struct CriticalSection<'a> {
    _internal_cs: &'a cortex_m::interrupt::CriticalSection,
}

impl<'a> CriticalSection<'a> {
    fn new(internal_cs: &'a cortex_m::interrupt::CriticalSection) -> Self {
        Self {
            _internal_cs: internal_cs,
        }
    }
}

/// Lock critical section for the duration of passed `f` closure
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate nrf_radio;
/// # missing_test_fns!();
/// # fn main() {
/// use nrf_radio::crit_sect;
///
/// crit_sect::locked(|cs_token| {
///   // Closure interior owns critical section token, so it can safely access variables guarded by
///   // the critical section. It can prove that accessing these variables from this content is
///   // safe by borrowing the token to whoever would need such proof (some Mutex?)
/// });
/// # }
/// ```
pub fn locked<F, R>(f: F) -> R
where
    F: FnOnce(&CriticalSection) -> R,
{
    // TODO: instead of disabling all interrupts, disable only relevant
    cortex_m::interrupt::free(|cs| f(&CriticalSection::new(cs)))
}
