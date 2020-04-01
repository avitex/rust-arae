![Project Status](https://img.shields.io/badge/status-experimental-red)
[![Build Status](https://travis-ci.org/avitex/rust-arae.svg?branch=master)](https://travis-ci.org/avitex/rust-arae)
[![Crate](https://img.shields.io/crates/v/arae.svg)](https://crates.io/crates/arae)
[![Docs](https://docs.rs/arae/badge.svg)](https://docs.rs/arae)

# rust-arae

**Cursed data structures**  
Documentation hosted on [docs.rs](https://docs.rs/arae).

## Experimental

> **Until otherwise noted, this library is experimental. Unsound issues should be assumed until fixed and verified**

```toml
[dependencies]
arae = "0.2.0"
```

## Example

```rust
use arae::{CurVec, CursedExt, Bounded};

// Create a new `CurVec` of length 10 with the elements 
// initialized via `Default::default`.
let mut vec = CurVec::new_with_default(10);

// Create two cursors pointing the the head of the vec.
let write_cursor = vec.hptr();
let read_cursor = vec.hptr();

*vec.get_mut(write_cursor) = 1;

assert_eq!(*vec.get(read_cursor), 1);
```
