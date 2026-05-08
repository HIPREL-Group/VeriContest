impl Solution {
    pub fn is_one_bit_character(bits: Vec<i32>) -> bool 
    {
        let n = bits.len();

        let mut i = 0;
        while (i < n - 1) 
        {
            i += 1 + (bits[i] as usize);
        }

        i == n - 1
    }
}
