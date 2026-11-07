impl Solution {
    pub fn sum_indices_with_k_set_bits(nums: Vec<i32>, k: i32) -> i32 {
        let mut res: i128 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            let mut t: usize = i;
            let mut b: usize = 0;
            let mut cnt: i32 = 0;
            while b < 10 {
                if t % 2 == 1 {
                    cnt = cnt + 1;
                }
                t = t / 2;
                b = b + 1;
            }
            let add: i128 = if cnt == k { nums[i] as i128 } else { 0 };
            res = res + add;
            i = i + 1;
        }
        res as i32
    }
}
