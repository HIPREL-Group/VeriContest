use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn exact_count(k: int) -> int
    decreases k
{
    if k <= 0 || k > 10 {
        0
    } else if k == 1 {
        9
    } else {
        exact_count(k - 1) * (11 - k)
    }
}

pub open spec fn total_unique(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        total_unique(n - 1) + exact_count(n)
    }
}

proof fn lemma_total_values()
    ensures
        total_unique(0) == 1,
        total_unique(1) == 10,
        total_unique(2) == 91,
        total_unique(3) == 739,
        total_unique(4) == 5275,
        total_unique(5) == 32491,
        total_unique(6) == 168571,
        total_unique(7) == 712891,
        total_unique(8) == 2345851,
{
    reveal_with_fuel(exact_count, 20);
    reveal_with_fuel(total_unique, 20);
    assert(exact_count(1) == 9);
    assert(exact_count(2) == 81);
    assert(exact_count(3) == 648);
    assert(exact_count(4) == 4536);
    assert(exact_count(5) == 27216);
    assert(exact_count(6) == 136080);
    assert(exact_count(7) == 544320);
    assert(exact_count(8) == 1632960);
    assert(total_unique(0) == 1);
    assert(total_unique(1) == 10);
    assert(total_unique(2) == 91);
    assert(total_unique(3) == 739);
    assert(total_unique(4) == 5275);
    assert(total_unique(5) == 32491);
    assert(total_unique(6) == 168571);
    assert(total_unique(7) == 712891);
    assert(total_unique(8) == 2345851);
}

impl Solution {
    pub fn count_numbers_with_unique_digits(n: i32) -> (result: i32)
        requires
            0 <= n <= 8,
        ensures
            result as int == total_unique(n as int),
    {
        proof {
            lemma_total_values();
        }
        if n == 0 {
            proof { assert(total_unique(n as int) == 1); }
            1
        } else if n == 1 {
            proof { assert(total_unique(n as int) == 10); }
            10
        } else if n == 2 {
            proof { assert(total_unique(n as int) == 91); }
            91
        } else if n == 3 {
            proof { assert(total_unique(n as int) == 739); }
            739
        } else if n == 4 {
            proof { assert(total_unique(n as int) == 5275); }
            5275
        } else if n == 5 {
            proof { assert(total_unique(n as int) == 32491); }
            32491
        } else if n == 6 {
            proof { assert(total_unique(n as int) == 168571); }
            168571
        } else if n == 7 {
            proof { assert(total_unique(n as int) == 712891); }
            712891
        } else {
            proof { assert(total_unique(n as int) == 2345851); }
            2345851
        }
    }
}

}
