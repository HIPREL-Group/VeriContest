impl Solution {
    fn score(nums: &Vec<i32>, d: i32) -> i32 {
        let mut i: usize = 0;
        let mut count: i32 = 0;
        while i < nums.len() {
            if nums[i] % d == 0 {
                count = count + 1;
            }
            i = i + 1;
        }
        count
    }

    pub fn max_div_score(nums: Vec<i32>, divisors: Vec<i32>) -> i32 {
        let mut best: i32 = divisors[0];
        let mut best_score: i32 = Self::score(&nums, best);

        let mut i: usize = 1;
        while i < divisors.len() {
            let cur = divisors[i];
            let cur_score = Self::score(&nums, cur);
            if cur_score > best_score || (cur_score == best_score && cur < best) {
                best = cur;
                best_score = cur_score;
            }
            i = i + 1;
        }

        best
    }
}
