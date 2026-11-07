use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_min(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn neighbor_min(s: Seq<i32>, i: int) -> int {
        let left = if i > 0 { s[i - 1] as int } else { 1001int };
        let right = if i + 1 < s.len() as int { s[i + 1] as int } else { 1001int };
        Self::spec_min(left, right)
    }

    pub open spec fn moves_at(s: Seq<i32>, i: int) -> int {
        Self::spec_max(0, s[i] as int - Self::neighbor_min(s, i) + 1)
    }

    pub open spec fn sum_moves(s: Seq<i32>, parity: int, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            Self::sum_moves(s, parity, end - 1) +
                if (end - 1) % 2 == parity { Self::moves_at(s, end - 1) } else { 0 }
        }
    }

    pub fn moves_to_make_zigzag(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums@.len() <= 1000,
            forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 1000,
        ensures
            result as int == Self::spec_min(
                Self::sum_moves(nums@, 0, nums@.len() as int),
                Self::sum_moves(nums@, 1, nums@.len() as int),
            ),
    {
        let n = nums.len();
        let mut res0: i32 = 0;
        let mut res1: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 1000,
                0 <= i <= n,
                forall |j: int| 0 <= j < n as int ==> 1 <= #[trigger] nums@[j] <= 1000,
                res0 as int == Self::sum_moves(nums@, 0, i as int),
                res1 as int == Self::sum_moves(nums@, 1, i as int),
                0 <= res0 as int <= i as int * 1000,
                0 <= res1 as int <= i as int * 1000,
            decreases n - i,
        {
            let left = if i > 0 { nums[i - 1] } else { 1001 };
            let right = if i + 1 < n { nums[i + 1] } else { 1001 };
            let min_neighbor = if left <= right { left } else { right };
            let moves = if nums[i] >= min_neighbor { nums[i] - min_neighbor + 1 } else { 0 };
            proof {
                assert(min_neighbor as int == Self::neighbor_min(nums@, i as int));
                assert(moves as int == Self::moves_at(nums@, i as int));
                assert(0 <= moves <= 1000);
            }
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

}
