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

pub open spec fn is_min_ops(a: Seq<i64>, n: usize, ans: i64) -> bool {
    ans >= 0 && ans < n &&
    can_partition_k(a, n, (n as int - ans as int)) &&
    forall|k2: int| k2 > (n as int - ans as int) && k2 <= n ==> !can_partition_k(a, n, k2)
}

proof fn lemma_sum_range_bounds(a: Seq<i64>, start: int, end: int)
    requires
        0 <= start && start <= end && end <= a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> 1 <= a[i] && a[i] <= 100000,
    ensures
        sum_range(a, start, end) >= (end - start),
        sum_range(a, start, end) <= (end - start) * 100000,
    decreases end - start
{
    if end > start {
        lemma_sum_range_bounds(a, start, end - 1);
    }
}

proof fn lemma_partition_one(a: Seq<i64>, n: usize)
    requires
        n >= 1,
        a.len() == n,
    ensures
        can_partition_k(a, n, 1),
{
    let splits: Seq<int> = seq![0, n as int];
    assert(splits.len() == 2);
    assert(splits[0] == 0);
    assert(splits[1] == n as int);
    assert(splits[0] < splits[1]);
    assert(sum_range(a, splits[0], splits[1]) == sum_range(a, 0, n as int));
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
        while i < n
            invariant
                0 <= i && i <= n,
                n <= 3000,
                a.len() == n,
                forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 100000,
                total as int == sum_range(a@, 0, i as int),
                total >= i as i64,
                total <= (i as i64) * 100000,
            decreases n - i
        {
            total += a[i];
            i += 1;
        }
        proof {
            lemma_sum_range_bounds(a@, 0, n as int);
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
        proof {
            lemma_sum_range_bounds(a@, 0, n as int);
            assert(total as int >= n as int);
            assert(n as int >= g as int);
            assert(total >= g as i64);
            assert(g >= 1);
            assert(total / (g as i64) >= 1) by (nonlinear_arith)
                requires total as int >= g as int, g as int >= 1;
        }
        let mut seg_sum: i64 = 0;
        let mut count: usize = 0;
        let mut j: usize = 0;
        let mut ok = true;
        let ghost mut splits: Seq<int> = seq![0];
        while j < n
            invariant
                0 <= j && j <= n,
                n <= 3000,
                a.len() == n,
                1 <= g && g <= n,
                forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
                total as int == sum_range(a@, 0, n as int),
                1 <= total && total <= 300000000,
                target == total / (g as i64),
                target >= 1,
                count <= j && count <= n,
                ok ==> 0 <= seg_sum && seg_sum < total,
                ok ==> (
                    splits.len() == count + 1 &&
                    splits[0] == 0 &&
                    0 <= splits[count as int] && splits[count as int] <= j &&
                    seg_sum as int == sum_range(a@, splits[count as int], j as int) &&
                    forall|m: int| 0 <= m && m < count ==>
                        splits[m] < splits[m + 1] &&
                        sum_range(a@, splits[m], #[trigger] splits[m + 1]) == target as int
                ),
            decreases n - j
        {
            if ok {
                proof {
                    lemma_sum_range_bounds(a@, splits[count as int], j as int + 1);
                }
                seg_sum += a[j];
            }
            j += 1;
            if ok && seg_sum == target {
                proof {
                    splits = splits.push(j as int);
                }
                count += 1;
                seg_sum = 0;
            } else if ok && seg_sum > target {
                ok = false;
            }
        }
        if ok && count == g && seg_sum == 0 {
            proof {
                if splits[count as int] < n as int {
                    lemma_sum_range_bounds(a@, splits[count as int], n as int);
                }
                assert(splits[count as int] == n as int);
                assert(can_partition_k(a@, n, g as int));
            }
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
        proof {
            lemma_partition_one(a@, n);
        }
        let mut g: usize = n;
        while g >= 1
            invariant
                0 <= g && g <= n,
                1 <= n && n <= 3000,
                a.len() == n,
                forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 100000,
                total as int == sum_range(a@, 0, n as int),
                1 <= total && total <= 300000000,
                1 <= best_k && best_k <= n,
                can_partition_k(a@, n, best_k as int),
            decreases g
        {
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
