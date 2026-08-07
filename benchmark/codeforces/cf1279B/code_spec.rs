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

    pub open spec fn gifts_from(a: Seq<i64>, n: int, s: int, skip_idx: int, i: int, acc: int, cnt: int) -> int
        decreases n - i,
    {
        if i >= n {
            cnt
        } else if i == skip_idx {
            Self::gifts_from(a, n, s, skip_idx, i + 1, acc, cnt)
        } else {
            let new_acc = acc + a[i];
            if new_acc > s {
                cnt
            } else {
                Self::gifts_from(a, n, s, skip_idx, i + 1, new_acc, cnt + 1)
            }
        }
    }

    pub open spec fn gifts(a: Seq<i64>, n: int, s: int, skip: int) -> int {
        Self::gifts_from(a, n, s, skip - 1, 0, 0, 0)
    }

    pub fn verse_for_santa(n: usize, s: i64, a: Vec<i64>) -> (res: i32)
        requires
            1 <= n <= 100000,
            a.len() == n,
            forall|i: int|
                #![trigger a[i]]
                0 <= i && i < n ==> 1 <= a[i] && a[i] <= 1000000000,
            1 <= s <= 1000000000,
        ensures
            Self::sum_all(a@, n as int) <= s as int ==> res == 0,
            Self::sum_all(a@, n as int) > s as int ==> {
                &&& 1 <= res as int <= n as int
                &&& forall|skip: int|
                    0 <= skip <= n as int ==> #[trigger] Self::gifts(a@, n as int, s as int, skip)
                        <= Self::gifts(a@, n as int, s as int, res as int)
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
