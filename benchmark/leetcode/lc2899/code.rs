impl Solution {
    pub fn last_visited_integers(nums: Vec<i32>) -> Vec<i32> {
        let n = nums.len();
        let mut seen: Vec<i32> = Vec::new();
        let mut ans: Vec<i32> = Vec::new();
        let mut consecutive: usize = 0;
        let mut i: usize = 0;
        while i < n {
            let x = nums[i];
            if x == -1 {
                consecutive += 1;
                if consecutive <= seen.len() {
                    let idx = seen.len() - consecutive;
                    ans.push(seen[idx]);
                } else {
                    ans.push(-1);
                }
            } else {
                seen.push(x);
                consecutive = 0;
            }
            i += 1;
        }
        ans
    }
}
