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

        while i < n
            invariant
                n == nums.len(),
                nums.len() <= 2147483647usize,
                0 <= k,
                0 <= i <= n,
                forall |p: int| 0 <= p < result.len() ==> 0 <= #[trigger] result[p] < i as i32,
                forall |a: int, b: int| 0 <= a < b < result.len() ==> result[a] < result[b],
                forall |p: int| 0 <= p < result.len() ==> is_k_distant(nums@, key as int, k as int, #[trigger] result[p] as int),
                forall |idx: int| 0 <= idx < i as int && is_k_distant(nums@, key as int, k as int, idx) ==>
                    exists|p: int| 0 <= p < result.len() && #[trigger] result[p] as int == idx,
            decreases n - i,
        {
            let mut j: usize = 0;
            let mut found: bool = false;

            while j < n
                invariant
                    n == nums.len(),
                    0 <= i < n,
                    0 <= k,
                    0 <= j <= n,
                    found == exists|jj: int| 0 <= jj < j as int && (i as int - jj <= k as int && jj - i as int <= k as int) && nums@[jj] as int == key as int,
                decreases n - j,
            {
                let diff: usize = if i >= j { i - j } else { j - i };
                if nums[j] == key && diff <= k as usize {
                    found = true;
                }
                j = j + 1;
            }

            assert(found == is_k_distant(nums@, key as int, k as int, i as int));

            let ghost prev_result = result@;

            if found {
                result.push(i as i32);
                assert(result@.last() == i as i32);
                assert(forall |p: int| 0 <= p < prev_result.len() ==> result@[p] == #[trigger] prev_result[p]);
                // The new element covers idx == i
                assert(exists|p: int| 0 <= p < result.len() && #[trigger] result[p] as int == i as int);
                // Old elements cover idx < i
                assert(forall |idx: int| 0 <= idx < i as int && is_k_distant(nums@, key as int, k as int, idx) ==>
                    exists|p: int| 0 <= p < result.len() && #[trigger] result[p] as int == idx);
            } else {
                assert(!is_k_distant(nums@, key as int, k as int, i as int));
            }

            i = i + 1;
        }

        result
    }
}

}
