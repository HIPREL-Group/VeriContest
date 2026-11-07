impl Solution {
    fn bit_value(n: i32, div: i32) -> i32 {
        (n / div) % 2
    }

    pub fn even_odd_bit(n: i32) -> Vec<i32> {
        let even = Self::bit_value(n, 1) + Self::bit_value(n, 4) + Self::bit_value(n, 16)
            + Self::bit_value(n, 64) + Self::bit_value(n, 256) + Self::bit_value(n, 1024);
        let odd = Self::bit_value(n, 2) + Self::bit_value(n, 8) + Self::bit_value(n, 32)
            + Self::bit_value(n, 128) + Self::bit_value(n, 512);

        let mut result = Vec::new();
        result.push(even);
        result.push(odd);
        result
    }
}
