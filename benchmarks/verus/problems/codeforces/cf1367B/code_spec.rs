use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_odd_at_even(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = count_odd_at_even(a.subrange(0, last));
        if last % 2 == 0 && a[last] % 2 == 1 {
            prev + 1
        } else {
            prev
        }
    }
}

pub open spec fn count_even_at_odd(a: Seq<u32>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = count_even_at_odd(a.subrange(0, last));
        if last % 2 == 1 && a[last] % 2 == 0 {
            prev + 1
        } else {
            prev
        }
    }
}

impl Solution {
    pub fn min_swaps(n: usize, a: Vec<u32>) -> (result: i64)
        requires
            1 <= n <= 40,
            a.len() == n,
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1000u32,
        ensures
            count_odd_at_even(a@) == count_even_at_odd(a@) ==> result == count_odd_at_even(a@),
            count_odd_at_even(a@) != count_even_at_odd(a@) ==> result == -1i64,
    {
        let mut odd_at_even: i64 = 0;
        let mut even_at_odd: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if i % 2 == 0 && a[i] % 2 == 1 {
                odd_at_even += 1;
            } else if i % 2 == 1 && a[i] % 2 == 0 {
                even_at_odd += 1;
            }
            i += 1;
        }
        if odd_at_even == even_at_odd {
            odd_at_even
        } else {
            -1
        }
    }
}

}
