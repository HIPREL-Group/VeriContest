use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_subseq(nums: Seq<i32>, indices: Seq<int>, peak: int) -> bool {
        &&& indices.len() >= 3
        &&& 0 < peak < indices.len() - 1
        &&& (forall |k: int| 0 <= k < indices.len() ==> 0 <= (#[trigger] indices[k]) < nums.len())
        &&& (forall |k: int| 0 <= k < peak ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) < nums[indices[k + 1]])
        &&& (forall |k: int| peak <= k < indices.len() - 1 ==>
            indices[k] < indices[k + 1] && (#[trigger] nums[indices[k]]) > nums[indices[k + 1]])
    }

    pub fn minimum_mountain_removals(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000i32,
            exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() as int
                && nums[a] < nums[b] && nums[b] > nums[c],
        ensures
            result >= 0,
            exists |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                && indices.len() == nums.len() - result as int,
            forall |indices: Seq<int>, peak: int| Self::is_mountain_subseq(nums@, indices, peak)
                ==> indices.len() <= nums.len() - result as int,
    {
        let n = nums.len();

        let mut lis: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n {
            lis.push(1i32);
            idx = idx + 1;
        }

        let mut i: usize = 1;
        while i < n {
            let mut j: usize = 0;
            while j < i {
                if nums[j] < nums[i] {
                    if lis[j] + 1 > lis[i] {
                        lis.set(i, lis[j] + 1);
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }

        let mut lds: Vec<i32> = Vec::new();
        idx = 0;
        while idx < n {
            lds.push(1i32);
            idx = idx + 1;
        }

        let mut k: usize = 1;
        while k < n {
            let i_idx: usize = n - 1 - k;
            let mut j: usize = i_idx + 1;
            while j < n {
                if nums[j] < nums[i_idx] {
                    if lds[j] + 1 > lds[i_idx] {
                        lds.set(i_idx, lds[j] + 1);
                    }
                }
                j = j + 1;
            }
            k = k + 1;
        }

        let mut result: i32 = n as i32;
        let mut i2: usize = 0;
        while i2 < n {
            if lis[i2] > 1 && lds[i2] > 1 {
                let mountain_len: i32 = lis[i2] + lds[i2] - 1;
                let removals: i32 = n as i32 - mountain_len;
                if removals < result {
                    result = removals;
                }
            }
            i2 = i2 + 1;
        }

        result
    }
}

}
