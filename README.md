[![Build Status](https://travis-ci.org/avitex/rust-arae.svg)](https://travis-ci.org/avitex/rust-arae)
[![Crate](https://img.shields.io/crates/v/arae.svg)](https://crates.io/crates/arae)
[![Docs](https://docs.rs/arae/badge.svg)](https://docs.rs/arae)

# rust-arae

**Cursed data structures**  
Documentation hosted on [docs.rs](https://docs.rs/arae).

```toml
arae = "0.1.0"
```

## Example

```rust
use arae::{CurVec, Cursed, Bounded};

// Create a new `CurVec` of length 10 with the elements 
// initialized via `Default::default`.
let mut vec = CurVec::new_with_default(10);

// Create two cursors pointing the the head of the vec.
let write_cursor = vec.head();
let read_cursor = vec.head();

*vec.get_mut(write_cursor) = 1;

assert_eq!(*vec.get(read_cursor), 1);
```

## TODO

- Implement `Chain`.
- Implement `Cursed` for standard structures.
