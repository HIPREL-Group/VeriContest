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
        {
            if grumpy[i] == 0 {
                base = base + customers[i] as i64;
            }
            i = i + 1;
        }

        let mut window: i64 = 0;
        let mut j: usize = 0;
        while j < m
        {
            if grumpy[j] == 1 {
                window = window + customers[j] as i64;
            }
            j = j + 1;
        }

        let mut max_window: i64 = window;
        let mut k: usize = m;

        while k < n
        {
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

            window = window + new_right_val - old_left_val;

            if window > max_window {
                max_window = window;
            }
            k = k + 1;
        }

        let result = (base + max_window) as i32;
        result
    }
}

}
