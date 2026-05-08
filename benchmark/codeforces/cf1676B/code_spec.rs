use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_min_value(s: Seq<i64>, m: int) -> bool {
    &&& s.len() > 0
    &&& exists|j: int| 0 <= j < s.len() && s[j] as int == m
    &&& forall|j: int| 0 <= j < s.len() ==> m <= s[j] as int
}

pub open spec fn sum_decrease_with(s: Seq<i64>, end: int, m: int) -> int
    recommends
        0 <= end <= s.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        sum_decrease_with(s, end - 1, m) + (s[end - 1] as int - m)
    }
}

impl Solution {
    pub fn min_operations_to_equal(candies: Vec<i64>) -> (result: i64)
        requires
            1 <= candies.len() <= 50,
            forall|i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] as int <= 1_000_000_000,
        ensures
            exists|min_v: int| is_min_value(candies@, min_v)
                && result as int == sum_decrease_with(candies@, candies.len() as int, min_v),
    {
        let n = candies.len();
        let mut min_val = candies[0];
        let mut i: usize = 1;
        while i < n {
            if candies[i] < min_val {
                min_val = candies[i];
            }
            i += 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < n {
            ans += candies[i] - min_val;
            i += 1;
        }
        ans
    }
}

}
