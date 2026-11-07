use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn distinct(seq: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> #[trigger] seq[i] != #[trigger] seq[j]
}

pub open spec fn reversed_value(seq: Seq<i64>, l: int, r: int, i: int) -> i64
    recommends
        0 <= l <= r < seq.len(),
        0 <= i < seq.len(),
{
    if l <= i && i <= r {
        seq[l + r - i]
    } else {
        seq[i]
    }
}

pub open spec fn reversal_sorts(seq: Seq<i64>, l: int, r: int) -> bool
    recommends
        0 <= l <= r < seq.len(),
{
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] reversed_value(seq, l, r, i) <= reversed_value(seq, l, r, i + 1)
}

pub open spec fn exists_sorting_segment(seq: Seq<i64>) -> bool {
    exists|l: int, r: int| 0 <= l <= r < seq.len() && reversal_sorts(seq, l, r)
}

impl Solution {
    pub fn sort_the_array(nums: Vec<i64>) -> (result: Option<(usize, usize)>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            distinct(nums@),
        ensures
            result != None::<(usize, usize)> ==> {
                let seg = result.get_Some_0();
                1 <= seg.0 <= seg.1 <= nums.len()
                    && reversal_sorts(nums@, seg.0 as int - 1, seg.1 as int - 1)
            },
            result == None::<(usize, usize)> ==> !exists_sorting_segment(nums@),
    {
        let n = nums.len();
        let mut left = 0usize;
        while left + 1 < n && nums[left] <= nums[left + 1] {
            left += 1;
        }
        if left + 1 == n {
            return Some((1, 1));
        }
        let mut right = n - 1;
        while right > 0 && nums[right - 1] <= nums[right] {
            right -= 1;
        }
        let mut i = 0usize;
        while i + 1 < n {
            let a = if left <= i && i <= right {
                nums[right - (i - left)]
            } else {
                nums[i]
            };
            let j = i + 1;
            let b = if left <= j && j <= right {
                nums[right - (j - left)]
            } else {
                nums[j]
            };
            if a > b {
                return None;
            }
            i += 1;
        }
        Some((left + 1, right + 1))
    }
}

}
