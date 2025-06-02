use std::sync::{Arc, Condvar, Mutex};

use crate::error::Error;

#[derive(Clone)]
pub struct CondVar<T> {
    inner: Arc<(Mutex<Option<T>>, Condvar)>,
}
impl<T> CondVar<T> {
    pub fn new() -> Self {
        Self {
            inner: Arc::new((Mutex::new(None), Condvar::new())),
        }
    }
    pub fn send(&self, value: T) -> Result<(), Error> {
        let (lock, cvar) = &*self.inner;
        let mut data = lock.lock().map_err(|_| Error::Cancelled)?;
        *data = Some(value);
        cvar.notify_all();

        Ok(())
    }
    pub fn wait(&self) -> Result<T, Error> {
        let (lock, cvar) = &*self.inner;
        let mut data = lock.lock().map_err(|_| Error::Cancelled)?;

        while data.is_none() {
            data = cvar.wait(data).map_err(|_| Error::Cancelled)?;
        }

        data.take().ok_or(Error::Cancelled)
    }
}
