use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_position(pos: int, n: int, a: int, b: int) -> bool {
    pos - 1 >= a && n - pos <= b
}

pub open spec fn count_valid_positions(k: int, n: int, a: int, b: int) -> nat
    decreases k,
{
    if k <= 0 {
        0nat
    } else {
        count_valid_positions(k - 1, n, a, b)
            + if is_valid_position(k, n, a, b) { 1nat } else { 0nat }
    }
}

proof fn lemma_count_eq(k: int, n: int, a: int, b: int, min_pos: int)
    requires
        0 <= k <= n,
        1 <= n,
        0 <= a < n,
        0 <= b < n,
        min_pos == if a + 1 >= n - b { a + 1 } else { n - b },
    ensures
        count_valid_positions(k, n, a, b) ==
            if k >= min_pos { (k - min_pos + 1) as nat } else { 0nat },
    decreases k,
{
    if k > 0 {
        lemma_count_eq(k - 1, n, a, b, min_pos);
        if k >= min_pos {
            assert(k - 1 >= a);
            assert(n - k <= b);
            assert(is_valid_position(k, n, a, b));
        } else {
            if k - 1 < a {
                assert(!is_valid_position(k, n, a, b));
            } else {
                assert(k >= a + 1);
                assert(k < n - b);
                assert(n - k > b);
                assert(!is_valid_position(k, n, a, b));
            }
        }
    }
}

impl Solution {
    pub fn count_positions(n: i32, a: i32, b: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            0 <= a < n,
            0 <= b < n,
        ensures
            result as int == count_valid_positions(n as int, n as int, a as int, b as int),
            result >= 0,
            result <= n,
    {
        let min_pos = if a + 1 >= n - b { a + 1 } else { n - b };
        proof {
            lemma_count_eq(n as int, n as int, a as int, b as int, min_pos as int);
        }
        n - min_pos + 1
    }
}

}
