// TODO: Implement own mutex abstraction instead of relying on cortex_m blocking IRQs
//       It should block only IRQs which can enter this function

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

pub fn locked<F, R>(f: F) -> R
where
    F: FnOnce(&CriticalSection) -> R,
{
    // TODO: instead of disabling all interrupts, disable only relevant
    cortex_m::interrupt::free(|cs| f(&CriticalSection::new(cs)))
}
