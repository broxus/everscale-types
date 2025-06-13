use std::sync::{Arc, Condvar, Mutex};

#[derive(Clone)]
#[repr(transparent)]
pub struct Promise<T> {
    inner: Arc<(Mutex<Option<T>>, Condvar)>,
}

impl<T> Default for Promise<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Promise<T> {
    pub fn new() -> Self {
        Self {
            inner: Arc::new((Mutex::new(None), Condvar::new())),
        }
    }

    pub fn set(&self, value: T) {
        let (lock, cvar) = &*self.inner;
        let mut data = lock.lock().unwrap();
        *data = Some(value);
        cvar.notify_all();
    }

    pub fn wait_cloned(&self) -> T
    where
        T: Clone,
    {
        let (lock, cvar) = &*self.inner;
        let mut data = lock.lock().unwrap();
        loop {
            match &*data {
                None => data = cvar.wait(data).unwrap(),
                Some(value) => break value.clone(),
            }
        }
    }
}
