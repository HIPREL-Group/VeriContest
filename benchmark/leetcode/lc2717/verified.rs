use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_perm(nums: Seq<i32>) -> bool {
        let n = nums.len();
        &&& 2 <= n <= 50
        &&& forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= n
        &&& forall |i: int, j: int| 0 <= i < j < n ==> nums[i] != nums[j]
    }

    pub open spec fn is_pos_1(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() && nums[i] == 1
    }

    pub open spec fn is_pos_n(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() && nums[i] == nums.len() as i32
    }

    pub open spec fn semi_ordered_swaps(nums: Seq<i32>) -> int
        recommends
            Self::is_perm(nums),
            exists |i: int| Self::is_pos_1(nums, i),
            exists |i: int| Self::is_pos_n(nums, i),
    {
        let i1 = choose |i: int| Self::is_pos_1(nums, i);
        let inx = choose |i: int| Self::is_pos_n(nums, i);
        i1 + (nums.len() - 1 - inx) - if i1 > inx { 1int } else { 0int }
    }

    proof fn lemma_unique_pos_1(nums: Seq<i32>, i: int, j: int)
        requires
            Self::is_perm(nums),
            Self::is_pos_1(nums, i),
            Self::is_pos_1(nums, j),
        ensures
            i == j,
    {
        if i < j {
            assert(nums[i] != nums[j]);
            assert(nums[i] == 1);
            assert(nums[j] == 1);
            assert(false);
        } else if j < i {
            assert(nums[j] != nums[i]);
            assert(nums[j] == 1);
            assert(nums[i] == 1);
            assert(false);
        }
    }

    proof fn lemma_unique_pos_n(nums: Seq<i32>, i: int, j: int)
        requires
            Self::is_perm(nums),
            Self::is_pos_n(nums, i),
            Self::is_pos_n(nums, j),
        ensures
            i == j,
    {
        if i < j {
            assert(nums[i] != nums[j]);
            assert(nums[i] == nums.len() as i32);
            assert(nums[j] == nums.len() as i32);
            assert(false);
        } else if j < i {
            assert(nums[j] != nums[i]);
            assert(nums[j] == nums.len() as i32);
            assert(nums[i] == nums.len() as i32);
            assert(false);
        }
    }

    pub fn semi_ordered_permutation(nums: Vec<i32>) -> (result: i32)
        requires
            Self::is_perm(nums@),
            exists |i: int| Self::is_pos_1(nums@, i),
            exists |i: int| Self::is_pos_n(nums@, i),
        ensures
            result as int == Self::semi_ordered_swaps(nums@),
            0 <= result,
            result <= 2 * nums.len(),
    {
        let n = nums.len();

        let ghost p1 = choose |i: int| Self::is_pos_1(nums@, i);
        let ghost pn = choose |i: int| Self::is_pos_n(nums@, i);

        let mut i1: usize = 0;
        while i1 < n && nums[i1] != 1
            invariant
                n == nums.len(),
                Self::is_perm(nums@),
                Self::is_pos_1(nums@, p1),
                0 <= i1 <= n,
                (i1 as int) <= p1,
                forall |k: int| 0 <= k < i1 as int ==> nums[k] != 1,
            decreases n - i1,
        {
            proof {
                assert((i1 as int) != p1);
                assert((i1 as int) < p1);
            }
            i1 = i1 + 1;
        }
        proof {
            assert((i1 as int) <= p1);
            assert(i1 < n);
            assert(!(nums@[i1 as int] != 1));
            assert(nums@[i1 as int] == 1);
            assert(Self::is_pos_1(nums@, i1 as int));
            Self::lemma_unique_pos_1(nums@, i1 as int, p1);
            assert((i1 as int) == p1);
        }

        let mut inx: usize = 0;
        while inx < n && nums[inx] != n as i32
            invariant
                n == nums.len(),
                Self::is_perm(nums@),
                Self::is_pos_n(nums@, pn),
                0 <= inx <= n,
                (inx as int) <= pn,
                forall |k: int| 0 <= k < inx as int ==> nums[k] != n as i32,
            decreases n - inx,
        {
            proof {
                assert((inx as int) != pn);
                assert((inx as int) < pn);
            }
            inx = inx + 1;
        }
        proof {
            assert((inx as int) <= pn);
            assert(inx < n);
            assert(!(nums@[inx as int] != n as i32));
            assert(nums@[inx as int] == n as i32);
            assert(Self::is_pos_n(nums@, inx as int));
            Self::lemma_unique_pos_n(nums@, inx as int, pn);
            assert((inx as int) == pn);
        }

        let ans = i1 as i32 + (n as i32 - 1 - inx as i32) - if i1 > inx { 1 } else { 0 };
        proof {
            assert(0 <= i1 as int <= n as int - 1);
            assert(0 <= inx as int <= n as int - 1);
            assert(ans as int == i1 as int + (n as int - 1 - inx as int) - if i1 > inx { 1int } else { 0int });
            assert(ans as int == p1 + (n as int - 1 - pn) - if p1 > pn { 1int } else { 0int });
            assert(ans as int == Self::semi_ordered_swaps(nums@));
            assert(0 <= ans as int);
            assert(ans as int <= 2 * n as int);
        }

        i1 as i32 + (n as i32 - 1 - inx as i32) - if i1 > inx { 1 } else { 0 }
    }
}

}
