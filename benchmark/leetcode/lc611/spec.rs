use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn is_index_permutation(p: Seq<int>, n: int) -> bool {
        p.len() == n
            && forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n
            && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
    }

    pub open spec fn count_pairs_from(s: Seq<i32>, last: int, left: int, right: int) -> nat
        recommends
            0 <= left <= right <= last < s.len(),
        decreases if left < right { (right - left) as nat } else { 0nat }
    {
        if right <= 1 || left >= right {
            0nat
        } else {
            let mid = right - 1;
            if left < mid {
                if s[left] as int + s[mid] as int > s[last] as int {
                    (mid - left) as nat + Self::count_pairs_from(s, last, left, mid)
                } else {
                    Self::count_pairs_from(s, last, left + 1, right)
                }
            } else {
                0nat
            }
        }
    }

    pub open spec fn triangle_count_from(s: Seq<i32>, start_last: int) -> nat
        decreases if start_last <= s.len() { (s.len() - start_last + 1) as nat } else { 0nat }
    {
        if start_last >= s.len() {
            0nat
        } else {
            Self::count_pairs_from(s, start_last, 0, start_last)
                + Self::triangle_count_from(s, start_last + 1)
        }
    }

    pub open spec fn triangle_count(s: Seq<i32>) -> nat {
        if s.len() < 3 {
            0nat
        } else {
            Self::triangle_count_from(s, 2)
        }
    }

    pub fn triangle_number(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result >= 0,
            exists|sorted_nums: Seq<i32>, perm: Seq<int>|
                Self::sorted(sorted_nums)
                && Self::is_index_permutation(perm, nums.len() as int)
                && sorted_nums.len() == nums.len()
                && (forall|i: int| 0 <= i < nums.len() ==> #[trigger] sorted_nums[i] == nums[perm[i]])
                && result as nat == Self::triangle_count(sorted_nums),
    {
    }
}

}
