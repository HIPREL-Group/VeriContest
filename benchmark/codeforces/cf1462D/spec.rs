use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn sum_range(a: Seq<i64>, start: int, end: int) -> int
    decreases end - start
{
    if end <= start {
        0
    } else {
        a[end - 1] as int + sum_range(a, start, end - 1)
    }
}

pub open spec fn can_partition_k(a: Seq<i64>, n: usize, k: int) -> bool {
    k >= 1 && k <= n &&
    sum_range(a, 0, n as int) % k == 0 &&
    {
        let target = sum_range(a, 0, n as int) / k;
        exists|splits: Seq<int>|
            splits.len() == k + 1 &&
            splits[0] == 0 && splits[k] == n &&
            (forall|j: int| 0 <= j && j < k ==>
                splits[j] < splits[j + 1] &&
                sum_range(a, splits[j], #[trigger] splits[j + 1]) == target)
    }
}

pub struct Solution;

impl Solution {
    pub fn min_operations(n: usize, a: Vec<i64>) -> (ans: i64)
        requires
            1 <= n && n <= 3000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
        ensures
            ans >= 0 && ans < n,
            can_partition_k(a@, n, (n as int - ans as int)),
    {
    }
}

}
