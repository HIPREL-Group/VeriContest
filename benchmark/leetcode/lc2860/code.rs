impl Solution {
    pub fn count_ways(nums: Vec<i32>) -> i32 {
        let n = nums.len() as i32;
        let mut x: i32 = 0;
        let mut ways: i32 = 0;
        while x <= n {
            let mut lt: i32 = 0;
            let mut eq: i32 = 0;
            let mut i: i32 = 0;
            while i < n {
                if nums[i as usize] < x {
                    lt = lt + 1;
                }
                if nums[i as usize] == x {
                    eq = eq + 1;
                }
                i = i + 1;
            }
            if lt == x && eq == 0 {
                ways = ways + 1;
            }
            x = x + 1;
        }
        ways
    }
}
