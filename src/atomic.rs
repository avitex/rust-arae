#[cfg(feature = "loom")]
pub(crate) use loom::sync::atomic::{AtomicPtr, Ordering};

#[cfg(not(feature = "loom"))]
pub(crate) use core::sync::atomic::{AtomicPtr, Ordering};
