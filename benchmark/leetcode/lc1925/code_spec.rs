use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_square_triple(a: int, b: int, c: int) -> bool {
    a * a + b * b == c * c
}

pub open spec fn count_for_c(n: int, a: int, b: int, c: int) -> int
    decreases n - c + 1,
{
    if c > n {
        0
    } else {
        (if is_square_triple(a, b, c) { 1int } else { 0int }) + count_for_c(n, a, b, c + 1)
    }
}

pub open spec fn count_for_b(n: int, a: int, b: int) -> int
    decreases n - b + 1,
{
    if b > n {
        0
    } else {
        count_for_c(n, a, b, 1) + count_for_b(n, a, b + 1)
    }
}

pub open spec fn count_for_a(n: int, a: int) -> int
    decreases n - a + 1,
{
    if a > n {
        0
    } else {
        count_for_b(n, a, 1) + count_for_a(n, a + 1)
    }
}

impl Solution {
    pub fn count_triples(n: i32) -> (result: i32)
        requires
            1 <= n <= 250,
        ensures
            result == count_for_a(n as int, 1),
    {
        let max_sq: i32 = n * n;
        let mut is_sq: Vec<bool> = Vec::new();
        let mut idx: i32 = 0;
        while idx <= max_sq
        {
            is_sq.push(false);
            idx = idx + 1;
        }
        let mut c: i32 = 1;
        while c <= n
        {
            is_sq.set((c * c) as usize, true);
            c = c + 1;
        }
        let mut count: i32 = 0;
        let mut a: i32 = 1;
        while a <= n
        {
            let mut b: i32 = 1;
            while b <= n
            {
                let s: i32 = a * a + b * b;
                if s <= max_sq && is_sq[s as usize] {
                    count = count + 1;
                }
                b = b + 1;
            }
            a = a + 1;
        }
        count
    }
}

}
