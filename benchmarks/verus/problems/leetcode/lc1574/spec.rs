use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        0 <= lo <= hi <= s.len() as int
        && forall|k: int| lo <= k < hi - 1 ==> #[trigger] s[k] <= s[k + 1]
    }

    pub open spec fn removal_works(s: Seq<i32>, l: int, r: int) -> bool {
        &&& 0 <= l <= r <= s.len() as int
        &&& Self::is_non_decreasing_range(s, 0, l)
        &&& Self::is_non_decreasing_range(s, r, s.len() as int)
        &&& (0 < l && r < s.len() as int ==> s[l - 1] <= s[r])
    }

    pub fn find_length_of_shortest_subarray(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 100_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
        ensures
            0 <= result <= arr.len() as i32,
            exists|l: int, r: int| Self::removal_works(arr@, l, r) && result as int == r - l,
            forall|l: int, r: int| Self::removal_works(arr@, l, r) ==> result as int <= r - l,
    {
    }
}

}
