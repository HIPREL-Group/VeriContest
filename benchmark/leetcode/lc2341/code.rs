impl Solution {
    pub fn number_of_pairs(nums: Vec<i32>) -> Vec<i32> {
        let mut cnt: Vec<i32> = vec![0; 101];
        let mut i: usize = 0;
        while i < nums.len() {
            let x = nums[i] as usize;
            cnt[x] = cnt[x] + 1;
            i = i + 1;
        }

        let mut pairs: i32 = 0;
        let mut leftover: i32 = 0;
        i = 0;
        while i <= 100 {
            pairs = pairs + cnt[i] / 2;
            leftover = leftover + cnt[i] % 2;
            i = i + 1;
        }
        vec![pairs, leftover]
    }
}
