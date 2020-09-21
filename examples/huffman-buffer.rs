/// Compare two normal styles of implementing tree traversal.
///
/// This uses the static `Constant` style, a dependent version with dynamic
/// buffer sizes might also be possible but requires non-`'static` structs.
///
/// This implements a semi-realistic style for Huffman coding with 8-bit node
/// arity. We have a tree in memory by storing the parent of all nodes and its
/// relative index, which is also its output symbol. A symbol is encoded by
/// following its path to the root and concatenating all bytes on the way. This
/// is done in three styles, each with 1k warm up iterations and then 1M
/// iterations summing their execution time.
///
/// Firstly, using safe Rust code and only the standard library. This does
/// many of the bounds checks at runtime. Judging from the generated
/// assembly, llvm is unable to remember (or check) that indices stored in
/// `parent` are in-bounds of the arrays. Hence when loading them it treats
/// them as an opaque value and does the usual checks against the length.
///
/// The second one uses unsafe Rust code, that one should conventionally
/// avoid to write, asserting to the compiler that we've not stored any
/// invalid parent indices. But this fact is not validated in any way and
/// requires quite a lot of trust in not changing the array sizes. However,
/// it is shown to be faster—at least on all machines I've tested it on.
///
/// And finally one last style that uses the library. It encodes the allowed
/// range of indices into that special `Idx<_, Tag>` type, and they are
/// checked at construction. But when loading them from the `parent` array
/// we do not need to rely on llvm's ability to see their value range so we
/// have effectively moved the index check of the access to compile time.
/// This retains the performance of the unsafe style with the additional
/// safety against buffer size changes.
///
/// The one thing to look for is the code for `code_of`/`code_of_unchecked`.
/// The arrays parents and bytes are accessed with the `[idx]` operator in
/// the style, with `get_unchecked` in the second and with `get_safe` in the
/// last, otherwise their code is identical.
///
use index_ext::tag::{Boxed, Constant, ConstantSource, ExactSize, Idx};

const BUFFER_SIZE: usize = 4096;
struct BufferSize4K;

impl ConstantSource for BufferSize4K {
    const LEN: usize = BUFFER_SIZE;
}

const LEN: ExactSize<Constant<BufferSize4K>> = Constant::EXACT_SIZE;

type ParentId = Idx<usize, Constant<BufferSize4K>>;

/// A 8-byte Huffman encoding tree.
/// Each entry points to its is ensured to point into the `parents` buffer.
struct HuffmanTree {
    parents: Boxed<ParentId, Constant<BufferSize4K>>,
    bytes: Boxed<u8, Constant<BufferSize4K>>,
}

fn main() {
    let huffman = HuffmanTree::new();
    let compare = Comparison::new();

    let codes: Vec<_> = (0..BUFFER_SIZE).collect();

    // Try to make the numbers slightly more predictable? Dynamic frequency
    // scaling (due to heat etc.) will ruin these.
    #[cfg(target_family = "unix")]
    unsafe {
        let mut set: libc::cpu_set_t = core::mem::zeroed();
        libc::CPU_ZERO(&mut set);
        libc::CPU_SET(0, &mut set);
        libc::sched_setaffinity(0, 1, &set);
    }

    // The classic, checked method.
    for _ in 0..1_000 {
        for &code in &codes {
            let _ = compare.code_of(code);
        }
    }
    let start = std::time::Instant::now();
    let mut side_effect = 0;
    for _ in 0..1_000_000 {
        for &code in &codes {
            side_effect |= compare.code_of(code);
        }
    }
    let duration = std::time::Instant::now()
        .duration_since(start)
        .as_secs_f32();
    println!(
        "With dynamically checked indices (safe): {}s ({})",
        duration, side_effect
    );

    // The unchecked, unsafe method.
    for _ in 0..1_000 {
        for &code in &codes {
            let _ = compare.code_of_unchecked(code);
        }
    }
    let start = std::time::Instant::now();
    let mut side_effect = 0;
    for _ in 0..1_000_000 {
        for &code in &codes {
            side_effect |= compare.code_of_unchecked(code);
        }
    }
    let duration = std::time::Instant::now()
        .duration_since(start)
        .as_secs_f32();
    println!(
        "With dynamically unchecked indices (ad-hoc unsafe): {}s ({})",
        duration, side_effect
    );

    // The safe, type tag checked method of this library.
    let codes: Vec<_> = (0..BUFFER_SIZE)
        .map(|i| LEN.len().index(i).unwrap())
        .collect();

    for _ in 0..1_000 {
        for &code in &codes {
            let _ = huffman.code_of(code);
        }
    }
    let start = std::time::Instant::now();
    let mut side_effect = 0;
    for _ in 0..1_000_000 {
        for &code in &codes {
            side_effect |= huffman.code_of(code);
        }
    }
    let duration = std::time::Instant::now()
        .duration_since(start)
        .as_secs_f32();
    println!(
        "With dependently checked indices (this crate): {}s ({})",
        duration, side_effect
    );
}

/// An alternative, with standard checked indexing.
struct Comparison {
    parents: Box<[usize; BUFFER_SIZE]>,
    bytes: Box<[u8; BUFFER_SIZE]>,
}

impl HuffmanTree {
    pub fn new() -> Self {
        let mut p: Vec<_> = generate_parent_indices()
            .map(|idx| LEN.len().index(idx).unwrap())
            .collect();

        // Zero-extend.
        let zero = LEN.len().index(0).unwrap();
        p.resize(BUFFER_SIZE, zero);
        let p = p.into_boxed_slice();

        let mut b = vec![0; BUFFER_SIZE].into_boxed_slice();
        for (p, b) in generate_bytes().zip(&mut b[..]) {
            *b = p;
        }

        HuffmanTree {
            parents: Boxed::new(p, LEN).unwrap_or_else(|_| panic!("Bad length of buffer")),
            bytes: Boxed::new(b, LEN).unwrap_or_else(|_| panic!("Bad length of buffer")),
        }
    }

    fn code_of(&self, start: ParentId) -> u64 {
        let mut enc: u64 = 0;
        let mut code = start;
        while {
            enc = (enc << 8) | u64::from(*self.bytes.get_safe(code));
            let more = code.into_inner() > 255;
            code = *self.parents.get_safe(code);
            more
        } {}
        enc
    }
}

impl Comparison {
    pub fn new() -> Self {
        let mut c = Comparison {
            parents: Box::new([0; BUFFER_SIZE]),
            bytes: Box::new([0; BUFFER_SIZE]),
        };

        for (p, b) in generate_parent_indices().zip(&mut c.parents[..]) {
            *b = p;
        }

        for (p, b) in generate_bytes().zip(&mut c.bytes[..]) {
            *b = p;
        }

        c
    }

    fn code_of(&self, start: usize) -> u64 {
        let mut enc: u64 = 0;
        let mut code = start;
        while {
            enc = (enc << 8) | u64::from(self.bytes[code]);
            let more = code > 255;
            code = self.parents[code];
            more
        } {}
        enc
    }

    fn code_of_unchecked(&self, start: usize) -> u64 {
        assert!(start < BUFFER_SIZE);
        unsafe {
            let mut enc: u64 = 0;
            let mut code = start;
            while {
                enc = (enc << 8) | u64::from(*self.bytes.get_unchecked(code));
                let more = code > 255;
                code = *self.parents.get_unchecked(code);
                more
            } {}
            enc
        }
    }
}

fn generate_parent_indices() -> impl Iterator<Item = usize> {
    std::iter::repeat(0)
        .take(256)
        .chain((0..3).map(|i| std::iter::repeat(i).take(256)).flatten())
        .chain({
            (0..4)
                .map(|i| std::iter::repeat(256 + i).take(256))
                .flatten()
        })
        .chain({
            (0..8)
                .map(|i| std::iter::repeat(1024 + i).take(256))
                .flatten()
        })
}

fn generate_bytes() -> impl Iterator<Item = u8> {
    std::iter::repeat((0..=255).into_iter()).flatten()
}
