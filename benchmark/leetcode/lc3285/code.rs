impl Solution {
    pub fn stable_mountains(height: Vec<i32>, threshold: i32) -> Vec<i32> {
        let mut ans = Vec::new();
        let mut i: usize = 1;
        while i < height.len() {
            if height[i - 1] > threshold {
                ans.push(i as i32);
            }
            i += 1;
        }
        ans
    }
}
