impl Solution {
    pub fn kids_with_candies(candies: Vec<i32>, extra_candies: i32) -> Vec<bool> {
        let n = candies.len();
        let mut max_candies = candies[0];
        let mut max_index: usize = 0;
        let mut i: usize = 1;

        while i < n {
            if candies[i] > max_candies {
                max_candies = candies[i];
                max_index = i;
            }
            i = i + 1;
        }

        let threshold = candies[max_index] - extra_candies;
        let mut result: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            let can_have_most = candies[k] >= threshold;
            result.push(can_have_most);
            k = k + 1;
        }

        result
    }
}