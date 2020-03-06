[![Build Status](https://travis-ci.org/avitex/rust-carousel.svg)](https://travis-ci.org/avitex/rust-carousel)
[![Crate](https://img.shields.io/crates/v/carousel.svg)](https://crates.io/crates/carousel)
[![Docs](https://docs.rs/carousel/badge.svg)](https://docs.rs/carousel)

# carousel

**A cyclic data structure in contiguous memory**  
Documentation hosted on [docs.rs](https://docs.rs/carousel).

```toml
carousel = "0.1.0"
```

## Example

```rust
use carousel::Ring;

// Create a new `Ring` of length 10 with the elements 
// initialized via `Default::default`.
let mut ring = Ring::new_with_default(10);

// Create two cursors pointing the the head of the ring.
let write_cursor = ring.head();
let read_cursor = ring.head();

*ring.get_mut(write_cursor) = 1;

assert_eq!(*ring.get(read_cursor), 1);
```
