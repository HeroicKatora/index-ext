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
    parents: [usize; BUFFER_SIZE],
    bytes: [u8; BUFFER_SIZE],
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
            parents: [0; BUFFER_SIZE],
            bytes: [0; BUFFER_SIZE],
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
