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
    fn compute_sum(n: usize, a: &Vec<i64>) -> (total: i64)
        requires
            1 <= n && n <= 3000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
        ensures
            total as int == sum_range(a@, 0, n as int),
            1 <= total && total <= 300000000,
    {
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            total += a[i];
            i += 1;
        }
        total
    }

    fn check_partition(n: usize, a: &Vec<i64>, g: usize, total: i64) -> (ok: bool)
        requires
            1 <= g && g <= n && n <= 3000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
            total as int == sum_range(a@, 0, n as int),
            1 <= total && total <= 300000000,
            total % (g as i64) == 0,
            total >= g as i64,
        ensures
            ok ==> can_partition_k(a@, n, g as int),
    {
        let target = total / (g as i64);
        let mut seg_sum: i64 = 0;
        let mut count: usize = 0;
        let mut j: usize = 0;
        let mut ok = true;
        while j < n {
            if ok {
                seg_sum += a[j];
            }
            j += 1;
            if ok && seg_sum == target {
                count += 1;
                seg_sum = 0;
            } else if ok && seg_sum > target {
                ok = false;
            }
        }
        if ok && count == g && seg_sum == 0 {
            true
        } else {
            false
        }
    }

    pub fn min_operations(n: usize, a: Vec<i64>) -> (ans: i64)
        requires
            1 <= n && n <= 3000,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
        ensures
            ans >= 0 && ans < n,
            can_partition_k(a@, n, (n as int - ans as int)),
    {
        let total = Solution::compute_sum(n, &a);
        let mut best_k: usize = 1;
        let mut g: usize = n;
        while g >= 1 {
            if total % (g as i64) == 0 && total >= g as i64 {
                let ok = Solution::check_partition(n, &a, g, total);
                if ok {
                    best_k = g;
                    return (n as i64) - (best_k as i64);
                }
            }
            g -= 1;
        }
        (n as i64) - (best_k as i64)
    }
}

}
