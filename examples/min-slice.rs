use index_ext::tag::{Constant, ConstantSource, Mut};

// This method accepts only slices at least 10 elements long.
pub fn foo1(mut a: Mut<u8, Constant<Min10>>) {
    let idx = Constant::<Min10>::EXACT_SIZE.into_len().range_to_self();
    // And can iterate over them without panicking.
    for i in a.get_safe_mut(idx) {
        *i = 0;
    }
}

// All of the overhead we have since it's not builtin..
pub struct Min10;
impl ConstantSource for Min10 {
    const LEN: usize = 10;
}

fn main() {
    let mut buffer = [0u8; 12];
    let buffer = Mut::new(&mut buffer[..], Constant::<Min10>::EXACT_SIZE).unwrap();
    foo1(buffer);
}
