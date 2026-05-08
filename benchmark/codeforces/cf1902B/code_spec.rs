use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn ceil_div_pos(a: int, b: int) -> int
        recommends
            a >= 0,
            b > 0,
    {
        if a % b == 0 {
            a / b
        } else {
            a / b + 1
        }
    }

    pub open spec fn max_rest_days_spec(n: int, p: int, l: int, t: int) -> int
        recommends
            n >= 1,
            p >= 1,
            l >= 1,
            t >= 1,
    {
        let tasks = (n + 6) / 7;
        let pairs = tasks / 2;
        let odd = tasks % 2;
        let pair_pts = l + 2 * t;
        let pair_total = pairs * pair_pts;
        let study_days = if p <= pair_total {
            Self::ceil_div_pos(p, pair_pts)
        } else {
            let rem = p - pair_total;
            if odd == 1 {
                let one_day_pts = l + t;
                if rem <= one_day_pts {
                    pairs + 1
                } else {
                    pairs + 1 + Self::ceil_div_pos(rem - one_day_pts, l)
                }
            } else {
                pairs + Self::ceil_div_pos(rem, l)
            }
        };
        n - study_days
    }

    pub fn max_rest_days(n: i64, p: i64, l: i64, t: i64) -> (res: i64)
        requires
            1 <= n <= 100_000_000,
            1 <= p <= 10_000_000_000_000_000,
            1 <= l <= 1_000_000_000,
            1 <= t <= 1_000_000_000,
            ((n + 6) / 7 / 2) * (l + 2 * t) <= 9_000_000_000_000_000_000,
            p <= n * l + ((n + 6) / 7) * t,
        ensures
            res as int == Self::max_rest_days_spec(n as int, p as int, l as int, t as int),
    {
        let tasks: i64 = (n + 6) / 7;
        let pairs: i64 = tasks / 2;
        let odd: i64 = tasks % 2;
        let pair_pts: i64 = l + 2 * t;

        let pair_total: i64 = pairs * pair_pts;
        let mut study_days: i64;

        if p <= pair_total {
            if p % pair_pts == 0 {
                study_days = p / pair_pts;
            } else {
                study_days = p / pair_pts + 1;
            }
        } else {
            study_days = pairs;
            let mut rem: i64 = if p >= pair_total { p - pair_total } else { 0 };
            if odd == 1 {
                let one_day_pts: i64 = l + t;
                if rem <= one_day_pts {
                    study_days = study_days + 1;
                    rem = 0;
                } else {
                    study_days = study_days + 1;
                    rem = rem - one_day_pts;
                }
            }
            if rem > 0 {
                if rem % l == 0 {
                    study_days = study_days + rem / l;
                } else {
                    study_days = study_days + rem / l + 1;
                }
            }
        }

        n - study_days
    }
}

}
