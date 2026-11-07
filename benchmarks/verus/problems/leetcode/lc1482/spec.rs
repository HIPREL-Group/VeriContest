use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn token_prefix(bloom_day: Seq<i32>, day: int, k: int, i: int) -> int
        recommends
            0 <= i <= bloom_day.len(),
            k >= 1,
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            let prev = Self::token_prefix(bloom_day, day, k, i - 1);
            if bloom_day[i - 1] as int <= day {
                prev + 1
            } else {
                (prev / k) * k
            }
        }
    }

    pub open spec fn bouquets_by_day_spec(bloom_day: Seq<i32>, day: int, k: int) -> int
        recommends
            k >= 1,
    {
        Self::token_prefix(bloom_day, day, k, bloom_day.len() as int) / k
    }

    pub open spec fn can_make(bloom_day: Seq<i32>, day: int, m: int, k: int) -> bool
        recommends
            m >= 1,
            k >= 1,
    {
        Self::bouquets_by_day_spec(bloom_day, day, k) >= m
    }

    pub open spec fn max_prefix(bloom_day: Seq<i32>, n: int) -> int
        recommends
            1 <= n <= bloom_day.len(),
        decreases n,
    {
        if n <= 1 {
            bloom_day[0] as int
        } else {
            let prev = Self::max_prefix(bloom_day, n - 1);
            let cur = bloom_day[n - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn max_bloom(bloom_day: Seq<i32>) -> int
        recommends
            bloom_day.len() >= 1,
    {
        Self::max_prefix(bloom_day, bloom_day.len() as int)
    }

    fn bouquets_by_day(bloom_day: &Vec<i32>, day: i32, k: i32) -> (res: i32)
        requires
            1 <= bloom_day.len() <= 100_000,
            forall |i: int| 0 <= i < bloom_day.len() ==> 1 <= #[trigger] bloom_day[i] <= 1_000_000_000,
            1 <= day <= 1_000_000_000,
            1 <= k <= bloom_day.len(),
        ensures
            res as int == Self::bouquets_by_day_spec(bloom_day@, day as int, k as int),
    {
        
    }

    fn required_flowers(m: i32, k: i32) -> (need: u64)
        requires
            1 <= m <= 1_000_000,
            1 <= k <= 100_000,
        ensures
            need as int == (m as int) * (k as int),
    {
        
    }

    pub fn min_days(bloom_day: Vec<i32>, m: i32, k: i32) -> (res: i32)
        requires
            1 <= bloom_day.len() <= 100_000,
            forall |i: int| 0 <= i < bloom_day.len() ==> 1 <= #[trigger] bloom_day[i] <= 1_000_000_000,
            1 <= m <= 1_000_000,
            1 <= k <= bloom_day.len(),
        ensures
            (m as int) * (k as int) > bloom_day.len() ==> res == -1,
            (m as int) * (k as int) <= bloom_day.len() ==> (
                1 <= res <= Self::max_bloom(bloom_day@)
                && Self::can_make(bloom_day@, res as int, m as int, k as int)
                && forall |d: int| 1 <= d < res ==> !Self::can_make(bloom_day@, d, m as int, k as int)
            ),
    {
        
    }
}

}
