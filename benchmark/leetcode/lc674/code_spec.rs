use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_strictly_increasing(nums: Seq<i32>, start: int, len: int) -> bool
    {
        forall |j: int| start <= j < start + len - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub fn find_length_of_lcis(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= res,
            res as int <= nums.len(),
            exists |start: int|
                0 <= start && start + res as int <= nums.len() as int &&
                #[trigger] Self::is_strictly_increasing(nums@, start, res as int),
            forall |start: int, len: int|
                0 <= start && 1 <= len && start + len <= nums.len() as int &&
                len > res as int ==>              
                !#[trigger] Self::is_strictly_increasing(nums@, start, len),
    {
        let n = nums.len();
        let mut best: i32 = 1;
        let mut cur: i32 = 1;
        let mut i = 1usize;
        while i < n {
            if nums[i] > nums[i - 1] {
                cur = cur + 1;
                if cur > best {
                    best = cur;
                }
            } else {
                cur = 1;
            }
            i = i + 1;
        }
        best
    }
}

} 
