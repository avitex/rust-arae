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
use arae::Ring;

// Create a new `Ring` of length 10 with the elements 
// initialized via `Default::default`.
let mut ring = Ring::new_with_default(10);

// Create two cursors pointing the the head of the ring.
let write_cursor = ring.head();
let read_cursor = ring.head();

*ring.get_mut(write_cursor) = 1;

assert_eq!(*ring.get(read_cursor), 1);
```
