impl Solution {
    pub fn total_hamming_distance(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total = 0;
        let mut i: usize = 0;
        while i < n {
            let mut j = i + 1;
            while j < n {
                let mut xor = (nums[i] ^ nums[j]) as u32;
                let mut count: u32 = 0;
                while xor != 0 {
                    count += (xor % 2);
                    xor /= 2;
                }
                total += count as i32;
                j += 1;
            }
            i += 1;
        }
        total
    }
}
