# index-ext

A crate for flexible indexing.

## Automatic index type conversion

This crate makes it ergonomic to use arbitrary integer types as indices. This
is especially important for libraries where indices are dictated by an external
standard. Another reason could be platform or performance requirements due to
which `usize` is the wrong choice. With the types and trait provided here, this
just works for smaller and larger integer types than `usize`.

```rust
use index_ext::Int;
let buffer = [0; 256];
assert_eq!(buffer[Int(255_u8)], 0);
assert_eq!(buffer[Int(255_i32)], 0);
assert_eq!(buffer.get_int(-1_i8), None);
assert_eq!(buffer.get_int(u128::max_value()), None);
```

## Statically checked indices

The concept of tags, a type identifying a unique slice length, allows one to
proof through the type system that some integer is a valid index for a slice.
There are two ways to use it safely, by borrowing the original slice and
generative lifetimes or by using compile time constants, and one way to
unsafely use arbitrary types.

```rust
use index_ext::tag;

tag::with_ref(&[0, 1, 2, 3][..], |slice, len| {
  // Index construction is checked/fallible..
  let idx = len.index(2).unwrap();

  // But use is NOT. The method get_safe does no runtime checks.
  assert_eq!(*slice.get_safe(idx), 2);
});
```

This looks less impressive than it is because any short example is also caught
by the value range analysis of the optimizer. However, you can safely store
these indices in structures and pass them across function boundaries without
fail and you get a _guarantee_ that the access check is elided. See the Huffman
example for a use case with real differences.

## Nightly dependent features

Const generics promise to provide even more possibilities. Currently, when one
wants to reference a statically sized array within a dynamic slice then best
choices are not the most ergonomic ones. On very recent nightly Rust we can
leverage parameter deduction and const generics to design an index type that
combines the best aspects.

```rust
use index_ext::array::RangeTo;
let rgba = [0; 4];
let rgb: [u8; 3] = rgba[RangeTo];
let [r, g, b] = &rgba[RangeTo];
```

## License

Triple licensed under any of Apache-2.0, MIT, or zlib terms.
