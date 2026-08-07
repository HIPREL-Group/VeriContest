use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn even_index_sum(s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() < 2 {
            0int
        } else {
            s[0] as int + Self::even_index_sum(s.subrange(2, s.len() as int))
        }
    }

    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub fn array_pair_sum(nums: Vec<i32>) -> (result: i32)
        requires
            2 <= nums.len() <= 20000,
            nums.len() % 2 == 0,
            forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        ensures
            exists|sorted_nums: Seq<i32>|
                Self::sorted(sorted_nums)
                && sorted_nums.len() == nums.len()
                && Self::is_perm(sorted_nums, nums@)
                && result as int == Self::even_index_sum(sorted_nums),
    {
        let mut nums = nums;
        let n = nums.len();
        let mut i = 0usize;
        while i < n
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }

            let tmp = nums[i];
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            i += 1;
        }

        let mut sum: i32 = 0;
        let mut k = 0usize;
        let mut count: usize = 0;
        while k < n
        {
            sum = sum + nums[k];
            k += 2;
            count += 1;
        }

        sum
    }
}

}
