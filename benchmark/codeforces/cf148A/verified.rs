use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn damaged(i: int, k: int, l: int, m: int, n: int) -> bool {
    i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0
}

pub open spec fn count_damaged_spec(k: int, l: int, m: int, n: int, d: int) -> int
    decreases d,
{
    if d < 1 {
        0
    } else {
        let add: int = if damaged(d, k, l, m, n) { 1int } else { 0int };
        add + count_damaged_spec(k, l, m, n, d - 1)
    }
}

proof fn lemma_count_step(k: int, l: int, m: int, n: int, i: int)
    requires
        1 <= k,
        1 <= l,
        1 <= m,
        1 <= n,
        1 <= i,
    ensures
        count_damaged_spec(k, l, m, n, i) == count_damaged_spec(k, l, m, n, i - 1)
            + (if damaged(i, k, l, m, n) { 1int } else { 0int }),
    decreases i,
{
    reveal_with_fuel(count_damaged_spec, 2);
}

impl Solution {
    pub fn count_damaged(k: i32, l: i32, m: i32, n: i32, d: i32) -> (result: i32)
        requires
            1 <= k <= 10,
            1 <= l <= 10,
            1 <= m <= 10,
            1 <= n <= 10,
            1 <= d <= 100_000,
        ensures
            result as int == count_damaged_spec(k as int, l as int, m as int, n as int, d as int),
    {
        let mut count = 0i32;
        let mut i = 1i32;
        while i <= d
            invariant
                1 <= k <= 10,
                1 <= l <= 10,
                1 <= m <= 10,
                1 <= n <= 10,
                1 <= d <= 100_000,
                1 <= i <= d + 1,
                0 <= count <= i - 1,
                count as int == count_damaged_spec(k as int, l as int, m as int, n as int, (i - 1) as int),
            decreases (d - i + 1) as nat,
        {
            proof {
                lemma_count_step(k as int, l as int, m as int, n as int, i as int);
            }
            if i % k == 0 || i % l == 0 || i % m == 0 || i % n == 0 {
                count = count + 1;
            }
            proof {
                assert(count as int == count_damaged_spec(k as int, l as int, m as int, n as int, i as int));
            }
            i = i + 1;
        }
        count
    }
}

}
