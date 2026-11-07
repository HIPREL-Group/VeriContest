use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_valley_at(a: Seq<i64>, n: usize, l: int, r: int) -> bool {
    0 <= l && l <= r && r < n &&
    (forall|i: int| l <= i && i <= r ==> a[i] == a[l]) &&
    (l == 0 || a[l - 1] > a[l]) &&
    (r == n - 1 || a[r] < a[r + 1])
}

pub open spec fn has_unique_valley(a: Seq<i64>, n: usize) -> bool {
    exists|l: int, r: int| #![auto]
        is_valley_at(a, n, l, r) &&
        forall|l2: int, r2: int| is_valley_at(a, n, l2, r2) ==> l2 == l && r2 == r
}

pub struct Solution;

impl Solution {
    pub fn is_valley(n: usize, a: Vec<i64>) -> (count: i64)
        requires
            1 <= n && n <= 200000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 1000000000,
        ensures
            count >= 0,
            count == 1 <==> has_unique_valley(a@, n),
    {
        let mut count: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let block_start = i;
            while i < n && a[i] == a[block_start] {
                i += 1;
            }
            let block_end = i - 1;
            let left_ok = block_start == 0 || a[block_start - 1] > a[block_start];
            let right_ok = block_end == n - 1 || a[block_end] < a[block_end + 1];
            if left_ok && right_ok {
                count += 1;
            }
        }
        count
    }
}

}
