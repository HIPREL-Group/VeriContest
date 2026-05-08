use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn base_satisfied(customers: Seq<i32>, grumpy: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::base_satisfied(customers, grumpy, n - 1)
                + if grumpy[n - 1] == 0i32 { customers[n - 1] as int } else { 0int }
        }
    }

    pub open spec fn window_gain(customers: Seq<i32>, grumpy: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            (if grumpy[start] == 1i32 { customers[start] as int } else { 0int })
                + Self::window_gain(customers, grumpy, start + 1, end)
        }
    }

    pub open spec fn gain_at(customers: Seq<i32>, grumpy: Seq<i32>, s: int, m: int) -> int {
        Self::window_gain(customers, grumpy, s, s + m)
    }

    proof fn base_satisfied_bound(customers: Seq<i32>, grumpy: Seq<i32>, n: int)
        requires
            0 <= n <= customers.len(),
            n <= grumpy.len(),
            forall|i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 1000,
            forall|i: int| 0 <= i < grumpy.len() ==> (#[trigger] grumpy[i] == 0 || grumpy[i] == 1),
        ensures
            0 <= Self::base_satisfied(customers, grumpy, n) <= 1000 * n,
        decreases n,
    {
        if n > 0 {
            Self::base_satisfied_bound(customers, grumpy, n - 1);
        }
    }

    proof fn window_gain_nonneg(customers: Seq<i32>, grumpy: Seq<i32>, start: int, end: int)
        requires
            0 <= start,
            end <= customers.len(),
            end <= grumpy.len(),
            forall|i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 1000,
            forall|i: int| 0 <= i < grumpy.len() ==> (#[trigger] grumpy[i] == 0 || grumpy[i] == 1),
        ensures
            Self::window_gain(customers, grumpy, start, end) >= 0,
        decreases end - start,
    {
        if start < end {
            Self::window_gain_nonneg(customers, grumpy, start + 1, end);
        }
    }

    proof fn window_gain_upper(customers: Seq<i32>, grumpy: Seq<i32>, start: int, end: int)
        requires
            0 <= start <= end,
            end <= customers.len(),
            end <= grumpy.len(),
            forall|i: int| 0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 1000,
            forall|i: int| 0 <= i < grumpy.len() ==> (#[trigger] grumpy[i] == 0 || grumpy[i] == 1),
        ensures
            Self::window_gain(customers, grumpy, start, end) <= 1000 * (end - start),
        decreases end - start,
    {
        if start < end {
            Self::window_gain_upper(customers, grumpy, start + 1, end);
        }
    }

    proof fn window_gain_extend(
        customers: Seq<i32>,
        grumpy: Seq<i32>,
        start: int,
        end: int,
    )
        requires
            0 <= start <= end,
            end < customers.len(),
            end < grumpy.len(),
        ensures
            Self::window_gain(customers, grumpy, start, end + 1) == Self::window_gain(
                customers,
                grumpy,
                start,
                end,
            ) + (if grumpy[end] == 1i32 { customers[end] as int } else { 0int }),
        decreases end - start,
    {
        let add_end = if grumpy[end] == 1i32 {
            customers[end] as int
        } else {
            0int
        };
        if start < end {
            Self::window_gain_extend(customers, grumpy, start + 1, end);
            let add_start = if grumpy[start] == 1i32 {
                customers[start] as int
            } else {
                0int
            };
            assert(Self::window_gain(customers, grumpy, start, end + 1) == add_start
                + Self::window_gain(customers, grumpy, start + 1, end + 1));
            assert(Self::window_gain(customers, grumpy, start + 1, end + 1)
                == Self::window_gain(customers, grumpy, start + 1, end) + add_end);
            assert(Self::window_gain(customers, grumpy, start, end) == add_start
                + Self::window_gain(customers, grumpy, start + 1, end));
        } else {
            assert(Self::window_gain(customers, grumpy, start + 1, end + 1) == 0int);
            assert(Self::window_gain(customers, grumpy, start, end) == 0int);
        }
    }

    pub fn max_satisfied(customers: Vec<i32>, grumpy: Vec<i32>, minutes: i32) -> (result: i32)
        requires
            customers.len() == grumpy.len(),
            1 <= minutes <= customers.len() <= 20_000,
            forall|i: int|
                0 <= i < customers.len() ==> 0 <= #[trigger] customers[i] <= 1000,
            forall|i: int|
                0 <= i < grumpy.len() ==> (#[trigger] grumpy[i] == 0 || grumpy[i] == 1),
        ensures
            ({
                let n = customers.len() as int;
                let m = minutes as int;
                let base = Self::base_satisfied(customers@, grumpy@, n);
                &&& result >= 0
                &&& exists|s: int|
                    0 <= s <= n - m && result == base + #[trigger] Self::gain_at(
                        customers@,
                        grumpy@,
                        s,
                        m,
                    )
                &&& forall|s: int|
                    0 <= s <= n - m ==> result >= #[trigger] Self::gain_at(
                        customers@,
                        grumpy@,
                        s,
                        m,
                    ) + base
            }),
    {
        let n = customers.len();
        let m = minutes as usize;

        let mut base: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == customers.len(),
                n == grumpy.len(),
                n <= 20_000,
                forall|k: int|
                    0 <= k < customers.len() ==> 0 <= #[trigger] customers[k] <= 1000,
                forall|k: int|
                    0 <= k < grumpy.len() ==> (#[trigger] grumpy[k] == 0 || grumpy[k] == 1),
                base as int == Self::base_satisfied(customers@, grumpy@, i as int),
                0 <= base <= 20_000_000,
            decreases n - i,
        {
            proof {
                Self::base_satisfied_bound(customers@, grumpy@, i as int);
            }
            if grumpy[i] == 0 {
                base = base + customers[i] as i64;
            }
            i = i + 1;
            proof {
                Self::base_satisfied_bound(customers@, grumpy@, i as int);
            }
        }

        let mut window: i64 = 0;
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                m == minutes as usize,
                m <= n,
                n == customers.len(),
                n == grumpy.len(),
                n <= 20_000,
                forall|k: int|
                    0 <= k < customers.len() ==> 0 <= #[trigger] customers[k] <= 1000,
                forall|k: int|
                    0 <= k < grumpy.len() ==> (#[trigger] grumpy[k] == 0 || grumpy[k] == 1),
                window as int == Self::window_gain(customers@, grumpy@, 0, j as int),
                0 <= window <= 20_000_000,
            decreases m - j,
        {
            proof {
                Self::window_gain_extend(customers@, grumpy@, 0, j as int);
                Self::window_gain_nonneg(customers@, grumpy@, 0, j as int);
                Self::window_gain_upper(customers@, grumpy@, 0, j as int);
            }
            if grumpy[j] == 1 {
                window = window + customers[j] as i64;
            }
            j = j + 1;
            proof {
                Self::window_gain_nonneg(customers@, grumpy@, 0, j as int);
                Self::window_gain_upper(customers@, grumpy@, 0, j as int);
            }
        }

        let ghost mut best_start_ghost: int = 0;
        let mut max_window: i64 = window;
        let mut k: usize = m;

        while k < n
            invariant
                m <= k <= n,
                m == minutes as usize,
                1 <= m <= n,
                n == customers.len(),
                n == grumpy.len(),
                n <= 20_000,
                forall|idx: int|
                    0 <= idx < customers.len() ==> 0 <= #[trigger] customers[idx] <= 1000,
                forall|idx: int|
                    0 <= idx < grumpy.len() ==> (#[trigger] grumpy[idx] == 0 || grumpy[idx] == 1),
                window as int == Self::window_gain(
                    customers@,
                    grumpy@,
                    (k - m) as int,
                    k as int,
                ),
                0 <= window <= 20_000_000,
                max_window >= window,
                0 <= max_window <= 20_000_000,
                0 <= best_start_ghost <= (k - m) as int,
                max_window as int == Self::window_gain(
                    customers@,
                    grumpy@,
                    best_start_ghost,
                    best_start_ghost + m as int,
                ),
                forall|s: int|
                    0 <= s <= (k - m) as int ==> max_window >= #[trigger] Self::gain_at(
                        customers@,
                        grumpy@,
                        s,
                        m as int,
                    ),
            decreases n - k,
        {
            proof {
                Self::window_gain_extend(
                    customers@,
                    grumpy@,
                    (k - m) as int,
                    k as int,
                );
            }
            let new_right_val: i64 = if grumpy[k] == 1 {
                customers[k] as i64
            } else {
                0i64
            };
            let old_left_val: i64 = if grumpy[k - m] == 1 {
                customers[k - m] as i64
            } else {
                0i64
            };

            proof {
                let wg_old = Self::window_gain(
                    customers@,
                    grumpy@,
                    (k - m) as int,
                    k as int,
                );
                assert(Self::window_gain(
                    customers@,
                    grumpy@,
                    (k - m) as int,
                    k as int + 1,
                ) == wg_old + new_right_val);
                assert(Self::window_gain(
                    customers@,
                    grumpy@,
                    (k - m) as int,
                    k as int + 1,
                ) == old_left_val + Self::window_gain(
                    customers@,
                    grumpy@,
                    (k - m + 1) as int,
                    k as int + 1,
                ));
            }

            window = window + new_right_val - old_left_val;

            proof {
                Self::window_gain_nonneg(
                    customers@,
                    grumpy@,
                    (k + 1 - m) as int,
                    (k + 1) as int,
                );
                Self::window_gain_upper(
                    customers@,
                    grumpy@,
                    (k + 1 - m) as int,
                    (k + 1) as int,
                );
            }

            if window > max_window {
                max_window = window;
                proof {
                    best_start_ghost = (k + 1 - m) as int;
                }
            }
            k = k + 1;
        }

        proof {
            Self::base_satisfied_bound(customers@, grumpy@, n as int);
            Self::window_gain_nonneg(
                customers@,
                grumpy@,
                best_start_ghost,
                best_start_ghost + m as int,
            );
            Self::window_gain_upper(
                customers@,
                grumpy@,
                best_start_ghost,
                best_start_ghost + m as int,
            );
            assert(0 <= base + max_window <= 40_000_000);
            assert(max_window as int == Self::gain_at(
                customers@,
                grumpy@,
                best_start_ghost,
                m as int,
            ));
        }

        let result = (base + max_window) as i32;

        proof {
            assert(result == base as int + Self::gain_at(
                customers@,
                grumpy@,
                best_start_ghost,
                m as int,
            ));
        }

        result
    }
}

}
