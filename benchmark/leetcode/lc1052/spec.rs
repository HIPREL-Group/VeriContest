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
    }
}

}
