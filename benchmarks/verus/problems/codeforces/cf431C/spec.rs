use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn modulus() -> int {
    1_000_000_007
}

pub open spec fn sum_seq(parts: Seq<int>) -> int
    decreases parts.len(),
{
    if parts.len() == 0 {
        0
    } else {
        sum_seq(parts.drop_last()) + parts[parts.len() - 1]
    }
}

pub open spec fn valid_k_tree_sequence(parts: Seq<int>, total: int, k: int, d: int) -> bool
    recommends
        0 <= total,
        1 <= d <= k,
{
    &&& sum_seq(parts) == total
    &&& forall|i: int| 0 <= i < parts.len() ==> 1 <= #[trigger] parts[i] <= k
    &&& exists|i: int| 0 <= i < parts.len() && parts[i] >= d
}

pub open spec fn step_cap(total: int, k: int) -> int
    recommends
        0 <= total,
        1 <= k,
{
    if total < k { total } else { k }
}

pub open spec fn count_no_large_step(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else {
        count_no_large_step(total, k, d, step - 1)
            + if step < d {
                let rem = total - step;
                if rem == 0 {
                    1
                } else {
                    count_no_large_step(rem, k, d, step_cap(rem, k))
                }
            } else {
                0
            }
    }
}

pub open spec fn count_no_large(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        1
    } else {
        count_no_large_step(total, k, d, step_cap(total, k))
    }
}

pub open spec fn count_has_large_step(total: int, k: int, d: int, step: int) -> int
    recommends
        0 < total,
        1 <= d <= k,
        0 <= step <= step_cap(total, k),
    decreases total, step when 0 < total && 0 <= step && step <= total && 1 <= d && d <= k
{
    if step == 0 {
        0
    } else {
        count_has_large_step(total, k, d, step - 1)
            + if step < d {
                let rem = total - step;
                if rem == 0 {
                    0
                } else {
                    count_has_large_step(rem, k, d, step_cap(rem, k))
                }
            } else {
                let rem = total - step;
                if rem == 0 {
                    1
                } else {
                    count_no_large_step(rem, k, d, step_cap(rem, k))
                        + count_has_large_step(rem, k, d, step_cap(rem, k))
                }
            }
    }
}

pub open spec fn count_has_large(total: int, k: int, d: int) -> int
    recommends
        0 <= total,
        1 <= d <= k,
{
    if total == 0 {
        0
    } else {
        count_has_large_step(total, k, d, step_cap(total, k))
    }
}

impl Solution {
    pub fn count_k_tree_paths(n: i32, k: i32, d: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            1 <= d <= k <= 100,
        ensures
            0 <= result < modulus(),
            result as int == count_has_large(n as int, k as int, d as int) % modulus(),
    {
    }
}

}
