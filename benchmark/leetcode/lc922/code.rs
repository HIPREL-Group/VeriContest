impl Solution {
    pub fn sort_array_by_parity_ii(nums: Vec<i32>) -> Vec<i32>
    {
        let n = nums.len();
        let mut evens: Vec<i32> = Vec::new();
        let mut odds: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < n
        {
            if nums[i] % 2 == 0 {
                evens.push(nums[i]);
            } else {
                odds.push(nums[i]);
            }
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        while j < evens.len()
        {
            let even_v = evens[j];
            let odd_v = odds[j];
            result.push(even_v);
            result.push(odd_v);
            j = j + 1;
        }

        result
    }
}
