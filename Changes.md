## v1.0.0-beta.0

The const-generics related types and functions no longer require the `nightly`
feature and are now always enabled. This implies an MSRV of `1.52.0`.

The `Ref`/`Mut` is replaced with references to `Slice`, an in-place wrapper of
the internal slice.

Added `Boxed` versions for tagging a box as fulfilling the length requirements
of a slice relative to the length invariant associated with a tag.

Added interoperability with the `generativity` crate.

Added module `mem`, containing layout compatible transparent wrappers around
all primitive types that guarantee also being a valid `usize`.

## v0.0.2

Added module `tags`, a generativity based type system for pre-checked slice
indices that has no runtime overhead compared to `get_unchecked` but requires
some statically known types.

## v0.0.1

Initial version
