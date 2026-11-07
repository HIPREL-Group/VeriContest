use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn contribution(a: Seq<i32>, h: int, i: int) -> int
    recommends 0 <= i < a.len(),
{
    if a[i] <= h {
        1
    } else {
        2
    }
}

pub open spec fn total_width(a: Seq<i32>, n: int, h: int) -> int
    recommends 0 <= n <= a.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        total_width(a, n - 1, h) + contribution(a, h, n - 1)
    }
}

proof fn lemma_total_width_step(a: Seq<i32>, n: int, h: int)
    requires
        0 <= n < a.len(),
    ensures
        total_width(a, n + 1, h) == total_width(a, n, h) + contribution(a, h, n),
    decreases n,
{
    reveal_with_fuel(total_width, 3);
    reveal_with_fuel(contribution, 1);
}

impl Solution {
    pub fn total_road_width(a: Vec<i32>, n: usize, h: i32) -> (res: i32)
        requires
            1 <= n <= 1000,
            a.len() == n,
            1 <= h <= 1000,
            forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 2 * (h as int),
        ensures
            res as int == total_width(a@, n as int, h as int),
    {
        let mut sum = 0i32;
        let mut i = 0usize;
        while i < n
            invariant
                1 <= n <= 1000,
                a.len() == n,
                1 <= h <= 1000,
                forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 2 * (h as int),
                0 <= i <= n,
                sum as int == total_width(a@, i as int, h as int),
                0 <= sum as int <= 2 * (i as int),
            decreases n - i,
        {
            proof {
                lemma_total_width_step(a@, i as int, h as int);
            }
            if a[i] <= h {
                sum += 1;
            } else {
                sum += 2;
            }
            i += 1;
        }
        proof {
            assert(sum as int == total_width(a@, n as int, h as int));
            assert forall|i: int|
                0 <= i < n as int implies
                    (#[trigger] contribution(a@, h as int, i) == (if a@[i] <= h as int { 1int } else { 2int })) by {
                reveal_with_fuel(contribution, 1);
            }
        }
        sum
    }
}

}
