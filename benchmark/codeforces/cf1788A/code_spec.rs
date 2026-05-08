use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_twos_seq(a: Seq<i32>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        let add: int = if a[lo] == 2 { 1 } else { 0 };
        add + count_twos_seq(a, lo + 1, hi)
    }
}

pub open spec fn split_ok(a: Seq<i32>, n: int, k: int) -> bool {
    1 <= k <= n - 1 && count_twos_seq(a, 0, k) == count_twos_seq(a, k, n)
}

pub struct Solution;

impl Solution {
    pub fn one_and_two(n: usize, a: Vec<i32>) -> (res: i32)
        requires
            2 <= n <= 1000,
            n == a.len(),
            forall|i: int| 0 <= i < n as int ==> #[trigger] a[i] == 1 || a[i] == 2,
        ensures
            (res == -1) <==> (forall|k: int|
                1 <= k <= n as int - 1 ==> !#[trigger] split_ok(a@, n as int, k)),
            (res >= 1) <==> (exists|k: int|
                1 <= k <= n as int - 1 && #[trigger] split_ok(a@, n as int, k)),
            (res >= 1) <==> (split_ok(a@, n as int, res as int) && forall|j: int|
                1 <= j < res as int ==> !#[trigger] split_ok(a@, n as int, j)),
    {
        let mut total: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            if a[i] == 2 {
                total = total + 1;
            }
            i = i + 1;
        }
        if total % 2 != 0 {
            return -1;
        }
        let target: i32 = total / 2;
        let mut twos: i32 = 0;
        let mut k: usize = 1;
        while k < n {
            if a[k - 1] == 2 {
                twos = twos + 1;
            }
            if twos == target {
                return k as i32;
            }
            k = k + 1;
        }
        -1
    }
}

}
