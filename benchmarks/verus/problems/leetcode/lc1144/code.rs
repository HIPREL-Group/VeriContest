impl Solution {
    pub fn moves_to_make_zigzag(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut res0: i32 = 0;
        let mut res1: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            let left = if i > 0 { nums[i - 1] } else { 1001 };
            let right = if i + 1 < n { nums[i + 1] } else { 1001 };
            let min_neighbor = if left <= right { left } else { right };
            let moves = if nums[i] >= min_neighbor { nums[i] - min_neighbor + 1 } else { 0 };
            if i % 2 == 0 {
                res0 = res0 + moves;
            } else {
                res1 = res1 + moves;
            }
            i = i + 1;
        }
        if res0 <= res1 { res0 } else { res1 }
    }
}
