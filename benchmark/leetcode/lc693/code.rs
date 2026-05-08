impl Solution {
    pub fn has_alternating_bits(n: i32) -> bool {
        let nu: u32 = n as u32;
        let x: u32 = nu ^ (nu >> 1u32);
        x & (x + 1u32) == 0u32
    }
}
