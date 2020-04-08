# index-ext

A crate for flexible indexing.

## What the crate provides

This crate makes it ergonomic to use arbitrary integer types as indices. This
is especially important for libraries where indices are dictated by an external
standard. Another reason could be platform or performance requirements due to
which `usize` is the wrong choice. With the types and trait provided here, this
just works for smaller and larger integer types than `usize`.

```
use index_ext::Int;
let fine = [0u8; 2][Int(1u8)];
```

## Nightly dependent features

Const generics promise to provide even more possibilities. Currently, when one
wants to reference a statically sized array within a dynamic slice then best
choices are not the most ergonomic ones. On very recent nightly Rust we can
leverage parameter deduction and const generics to design an index type that
combines the best aspects.

```
use index_ext::array::Prefix;
let rgba = [0; 4];
let [r, g, b] = &rgb[Prefix];
```

## License

If you require this, then this is distributed under the terms of the [Unlicense].

[Unlicense]: UNLICENSE
