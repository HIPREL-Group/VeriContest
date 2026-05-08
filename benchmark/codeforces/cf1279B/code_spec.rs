use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(a: Seq<i64>, i: int) -> int
        decreases i + 1,
    {
        if i < 0 {
            0
        } else {
            a[i] + Self::prefix_sum(a, i - 1)
        }
    }

    pub open spec fn sum_all(a: Seq<i64>, n: int) -> int
        decreases n + 1,
    {
        if n <= 0 {
            0
        } else {
            Self::prefix_sum(a, n - 1)
        }
    }

    pub open spec fn min_overflow_from(a: Seq<i64>, n: int, s: int, i: int) -> int
        decreases n - i,
    {
        if i >= n {
            n
        } else if Self::prefix_sum(a, i) > s {
            i
        } else {
            Self::min_overflow_from(a, n, s, i + 1)
        }
    }

    pub open spec fn min_overflow_index(a: Seq<i64>, n: int, s: int) -> int {
        Self::min_overflow_from(a, n, s, 0)
    }

    pub open spec fn smallest_max_index_on_prefix(a: Seq<i64>, p: int) -> int
        decreases p + 1,
    {
        if p <= 0 {
            0
        } else {
            let prev = Self::smallest_max_index_on_prefix(a, p - 1);
            if a[p] > a[prev] {
                p
            } else {
                prev
            }
        }
    }

    pub open spec fn is_prefix_min_overflow(a: Seq<i64>, n: int, s: int, pos: int) -> bool {
        0 <= pos && pos < n && Self::prefix_sum(a, pos) > s
            && (forall|t: int| 0 <= t && t < pos ==> #[trigger] Self::prefix_sum(a, t) <= s)
    }

    pub open spec fn closed_answer(a: Seq<i64>, n: int, s: int) -> int {
        if Self::sum_all(a, n) <= s {
            0
        } else {
            Self::smallest_max_index_on_prefix(a, Self::min_overflow_index(a, n, s)) + 1
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> (res: i32)
        requires
            1 <= n <= 100000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n ==> 1 <= a[i] && a[i] <= 1000000000,
            1 <= s <= 1000000000,
        ensures
            res == Self::closed_answer(a@, n as int, s as int),
            Self::sum_all(a@, n as int) <= s as int ==> res == 0,
            Self::sum_all(a@, n as int) > s as int ==> {
                exists|pos: int|
                    Self::is_prefix_min_overflow(a@, n as int, s as int, pos) && pos
                        == Self::min_overflow_index(a@, n as int, s as int)
            },
    {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total = total + a[i];
            i = i + 1;
        }
        if total <= s {
            return 0;
        }
        let mut pref: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            pref = pref + a[j];
            if pref > s {
                let mut best_i: usize = 0;
                let mut t: usize = 1;
                while t <= j {
                    if a[t] > a[best_i] {
                        best_i = t;
                    }
                    t = t + 1;
                }
                return (best_i + 1) as i32;
            }
            j = j + 1;
        }
        0
    }
}

}
