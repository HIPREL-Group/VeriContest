use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn freq_at(requests: Seq<Vec<i32>>, idx: int, k: int) -> int
        decreases requests.len() - k
    {
        if k >= requests.len() as int {
            0
        } else {
            (if requests[k]@[0] as int <= idx && idx <= requests[k]@[1] as int {
                1int
            } else {
                0int
            }) + Self::freq_at(requests, idx, k + 1)
        }
    }

    pub open spec fn freq_vec(requests: Seq<Vec<i32>>, n: int) -> Seq<int> {
        Seq::new(n as nat, |i: int| Self::freq_at(requests, i, 0))
    }

    pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn dot_product_int(a: Seq<int>, b: Seq<int>, k: int) -> int
        decreases a.len() - k
    {
        if k >= a.len() as int {
            0
        } else {
            a[k] * b[k] + Self::dot_product_int(a, b, k + 1)
        }
    }

    pub open spec fn is_sorted_int(s: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_int(s: Seq<int>, v: int) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int })
                + Self::count_int(s.drop_last(), v)
        }
    }

    pub open spec fn is_perm_int(a: Seq<int>, b: Seq<int>) -> bool {
        a.len() == b.len()
            && forall |v: int| Self::count_int(a, v) == Self::count_int(b, v)
    }

    pub fn max_sum_range_query(nums: Vec<i32>, requests: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==>
                0 <= #[trigger] nums@[i] <= 100_000,
            1 <= requests@.len() <= 100_000,
            forall |i: int| 0 <= i < requests@.len() ==> (
                (#[trigger] requests@[i])@.len() == 2
                    && 0 <= requests@[i]@[0]
                    && requests@[i]@[0] <= requests@[i]@[1]
                    && (requests@[i]@[1] as int) < nums@.len() as int
            ),
        ensures
            0 <= result < 1_000_000_007,
            exists |sv: Seq<int>, sf: Seq<int>|
                sv.len() == nums@.len()
                && sf.len() == nums@.len()
                && Self::is_sorted_int(sv)
                && Self::is_sorted_int(sf)
                && Self::is_perm_int(sv, Self::to_int_seq(nums@))
                && Self::is_perm_int(sf, Self::freq_vec(requests@, nums@.len() as int))
                && result as int
                    == Self::dot_product_int(sv, sf, 0) % 1_000_000_007
                && forall |c: Seq<int>|
                    c.len() == sv.len() && Self::is_perm_int(c, sv)
                        ==> Self::dot_product_int(sv, sf, 0)
                            >= Self::dot_product_int(c, sf, 0),
    {
    }
}

}
