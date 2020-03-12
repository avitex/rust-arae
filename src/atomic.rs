#[cfg(feature = "loom")]
pub(crate) use loom::sync::atomic::*;

#[cfg(not(feature = "loom"))]
pub(crate) use core::sync::atomic::*;
