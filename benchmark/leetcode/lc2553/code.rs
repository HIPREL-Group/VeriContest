impl Solution {
    fn digits_exec(num: i32) -> Vec<i32> {
        if num < 10 {
            vec![num]
        } else {
            let mut rest = Self::digits_exec(num / 10);
            rest.push(num % 10);
            rest
        }
    }

    pub fn separate_digits(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut ans: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let d = Self::digits_exec(nums[i]);
            let mut j: usize = 0;
            while j < d.len() {
                ans.push(d[j]);
                j += 1;
            }
            i += 1;
        }
        ans
    }
}
