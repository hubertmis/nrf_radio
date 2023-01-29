use crate::crit_sect::CriticalSection;

pub struct Mutex<T> {
    inner: T,
}

impl <T> Mutex<T> {
    pub const fn new(value: T) -> Mutex<T> {
        Self {
            inner: value,
        }
    }

    pub fn borrow<'cs>(&'cs self, _cs: &'cs CriticalSection) -> &'cs T {
        &self.inner
    }
}

// TODO: Proper documentation
// Unsafety: Mutex is Sync assumming contained type is Send and the CriticalSection module prevents
// concurrent access to Mutex from multiple contexts. This assumption is verified run-time if
// RefCell is used inside the mutex
unsafe impl<T> Sync for Mutex<T> where T: Send {}
