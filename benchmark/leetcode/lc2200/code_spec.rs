use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_k_distant(nums: Seq<i32>, key: int, k: int, i: int) -> bool {
    exists|j: int| 0 <= j < nums.len() && (i - j <= k && j - i <= k) && nums[j] as int == key
}

impl Solution {
    pub fn find_k_distant_indices(nums: Vec<i32>, key: i32, k: i32) -> (result: Vec<i32>)
        requires
            nums.len() <= 2147483647usize,
            0 <= k,
        ensures
            forall |p: int| 0 <= p < result.len() ==> 0 <= #[trigger] result[p] < nums.len() as i32,
            forall |a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
            forall |p: int| 0 <= p < result.len() ==> is_k_distant(nums@, key as int, k as int, #[trigger] result[p] as int),
            forall |i: int| 0 <= i < nums@.len() && is_k_distant(nums@, key as int, k as int, i) ==>
                exists|p: int| 0 <= p < result.len() && #[trigger] result[p] as int == i,
    {
        let n = nums.len();
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            let mut found: bool = false;
            while j < n {
                let diff: usize = if i >= j { i - j } else { j - i };
                if nums[j] == key && diff <= k as usize {
                    found = true;
                }
                j = j + 1;
            }
            if found {
                result.push(i as i32);
            }
            i = i + 1;
        }
        result
    }
}

}
