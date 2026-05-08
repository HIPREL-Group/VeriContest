impl Solution {
    pub fn occurrences_of_element(nums: Vec<i32>, queries: Vec<i32>, x: i32) -> Vec<i32> {
        let mut positions: Vec<i32> = Vec::new();
        let mut i = 0usize;
        while i < nums.len() {
            if nums[i] == x {
                positions.push(i as i32);
            }
            i += 1;
        }

        let mut ans: Vec<i32> = Vec::new();
        let mut j = 0usize;
        while j < queries.len() {
            let q = queries[j] as usize;
            if q == 0 || q > positions.len() {
                ans.push(-1);
            } else {
                ans.push(positions[q - 1]);
            }
            j += 1;
        }
        ans
    }
}
