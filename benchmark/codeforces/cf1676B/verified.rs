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

proof fn lemma_sum_step(s: Seq<i64>, end: int, m: int)
    requires
        1 <= end <= s.len(),
    ensures
        sum_decrease_with(s, end, m) == sum_decrease_with(s, end - 1, m) + (s[end - 1] as int - m),
{
    reveal_with_fuel(sum_decrease_with, 2);
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
        while i < n
            invariant
                1 <= n <= 50,
                candies.len() == n,
                1 <= i <= n,
                forall|k: int| 0 <= k < candies.len() ==> 1 <= #[trigger] candies[k] as int <= 1_000_000_000,
                exists|j: int| 0 <= j < i as int && candies[j] == min_val,
                forall|j: int| 0 <= j < i as int ==> min_val <= candies[j],
            decreases n - i,
        {
            if candies[i] < min_val {
                min_val = candies[i];
            }
            i += 1;
        }

        let mut ans: i64 = 0;
        i = 0;
        while i < n
            invariant
                1 <= n <= 50,
                candies.len() == n,
                0 <= i <= n,
                forall|k: int| 0 <= k < candies.len() ==> 1 <= #[trigger] candies[k] as int <= 1_000_000_000,
                exists|j: int| 0 <= j < n as int && candies[j] == min_val,
                forall|j: int| 0 <= j < n as int ==> min_val <= candies[j],
                0 <= ans as int,
                ans as int <= i as int * 1_000_000_000,
                ans as int == sum_decrease_with(candies@, i as int, min_val as int),
            decreases n - i,
        {
            proof {
                assert(0 <= (i as int) && (i as int) < (n as int));
                lemma_sum_step(candies@, i as int + 1, min_val as int);
                assert(sum_decrease_with(candies@, i as int + 1, min_val as int)
                    == sum_decrease_with(candies@, i as int, min_val as int)
                        + (candies@[i as int] as int - min_val as int));
                assert(min_val as int <= candies@[i as int] as int);
                assert(0 <= candies@[i as int] as int - min_val as int);
                assert(candies@[i as int] as int <= 1_000_000_000);
                assert(min_val as int >= 1);
                assert(candies@[i as int] as int - min_val as int <= 1_000_000_000);
                assert(ans as int + (candies@[i as int] as int - min_val as int) <= (i as int + 1) * 1_000_000_000);
                assert(ans as int + (candies@[i as int] as int - min_val as int) < 9_223_372_036_854_775_807);
            }
            ans += candies[i] - min_val;
            proof {
                assert(ans as int == sum_decrease_with(candies@, i as int + 1, min_val as int));
                assert(ans as int <= (i as int + 1) * 1_000_000_000);
            }
            i += 1;
        }

        proof {
            assert(i == n);
            assert(ans as int == sum_decrease_with(candies@, candies.len() as int, min_val as int));
            assert(is_min_value(candies@, min_val as int));
        }

        ans
    }
}

}
