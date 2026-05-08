use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: int) -> int
    recommends
        n >= 0,
    decreases n,
{
    if n <= 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}

pub open spec fn bits_differ_at(x: int, y: int, j: int) -> bool
    recommends
        j >= 0,
        x >= 0,
        y >= 0,
{
    (x / pow2(j)) % 2 != (y / pow2(j)) % 2
}

pub open spec fn xor_popcount_prefix(x: int, y: int, bits_done: int) -> int
    recommends
        0 <= bits_done,
        x >= 0,
        y >= 0,
    decreases bits_done,
{
    if bits_done <= 0 {
        0
    } else {
        xor_popcount_prefix(x, y, bits_done - 1) + if bits_differ_at(x, y, bits_done - 1) {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn friend_count_prefix(
    armies: Seq<i32>,
    fedor: int,
    n: int,
    k: int,
    end: int,
) -> int
    recommends
        0 <= end <= armies.len(),
        forall|t: int| 0 <= t < end ==> #[trigger] armies[t] as int >= 0,
        fedor >= 0,
    decreases end,
{
    if end <= 0 {
        0
    } else {
        friend_count_prefix(armies, fedor, n, k, end - 1) + if xor_popcount_prefix(armies[end - 1] as int, fedor, n) <= k {
            1int
        } else {
            0int
        }
    }
}

impl Solution {
    fn xor_popcount_n(x: i32, y: i32, n_bits: i32) -> (c: i32)
        requires
            0 <= n_bits <= 20,
            0 <= x < 1048576,
            0 <= y < 1048576,
        ensures
            c as int == xor_popcount_prefix(x as int, y as int, n_bits as int),
    {
    }

    pub fn count_fedor_friends(n: i32, k: i32, armies: Vec<i32>) -> (res: i32)
        requires
            2 <= armies.len() && armies.len() <= 1001,
            0 <= (n as int) && 1 <= (k as int) && (k as int) <= (n as int) && (n as int) <= 20,
            forall|i: int|
                0 <= i < armies@.len() ==> (1 <= #[trigger] armies@[i] && (armies@[i] as int) < 1048576),
        ensures
            res as int == friend_count_prefix(
                armies@,
                armies@[(armies.len() as int) - 1] as int,
                n as int,
                k as int,
                armies.len() as int - 1,
            ),
    {
    }
}

}
