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

proof fn lemma_sum_range_additive(a: Seq<i64>, s: int, m: int, e: int)
    requires
        0 <= s <= m <= e <= a.len(),
    ensures
        sum_range(a, s, e) == sum_range(a, s, m) + sum_range(a, m, e),
    decreases e - m,
{
    if e > m {
        lemma_sum_range_additive(a, s, m, e - 1);
    }
}

proof fn lemma_sum_range_pos_strict(a: Seq<i64>, s: int, e: int)
    requires
        0 <= s < e <= a.len(),
        forall|i: int| s <= i < e ==> a[i] >= 1,
    ensures
        sum_range(a, s, e) >= e - s,
    decreases e - s,
{
    if e - 1 > s {
        lemma_sum_range_pos_strict(a, s, e - 1);
        assert(sum_range(a, s, e) == a[e - 1] as int + sum_range(a, s, e - 1));
    } else {
        assert(e - 1 == s);
        assert(sum_range(a, s, e) == a[e - 1] as int + sum_range(a, s, e - 1));
        assert(sum_range(a, s, e - 1) == 0);
        assert(a[e - 1] >= 1);
    }
}

proof fn lemma_sum_range_mono_strict(a: Seq<i64>, s: int, m: int, e: int)
    requires
        0 <= s <= m < e <= a.len(),
        forall|i: int| s <= i < a.len() ==> a[i] >= 1,
    ensures
        sum_range(a, s, m) < sum_range(a, s, e),
{
    lemma_sum_range_additive(a, s, m, e);
    lemma_sum_range_pos_strict(a, m, e);
}

proof fn lemma_seq_mono_le(splits: Seq<int>, bound: int, i: int, j: int)
    requires
        0 <= i <= j <= bound,
        bound < splits.len(),
        forall|k: int| 0 <= k < bound ==> splits[k] < #[trigger] splits[k + 1],
    ensures
        splits[i] <= splits[j],
    decreases j - i,
{
    if i < j {
        lemma_seq_mono_le(splits, bound, i, j - 1);
        let k = j - 1;
        assert(0 <= k < bound);
        assert(splits[k] < splits[k + 1]);
        assert(splits[i] <= splits[k]);
        assert(splits[j] == splits[k + 1]);
    } else {
        assert(i == j);
    }
}

proof fn lemma_sum_range_zero_implies_eq(a: Seq<i64>, m: int, pos: int)
    requires
        0 <= m <= pos <= a.len(),
        forall|i: int| m <= i < a.len() ==> a[i] >= 1,
        sum_range(a, m, pos) == 0,
    ensures
        m == pos,
{
    if m < pos {
        lemma_sum_range_pos_strict(a, m, pos);
        assert(false);
    }
}

pub open spec fn greedy_partition(a: Seq<i64>, target: int, pos: int, seg_sum: int, count: int, g: int) -> bool
    decreases a.len() - pos when 0 <= pos <= a.len()
{
    if pos >= a.len() {
        seg_sum == 0 && count == g
    } else {
        let new_sum = seg_sum + a[pos] as int;
        if new_sum == target {
            greedy_partition(a, target, pos + 1, 0, count + 1, g)
        } else if new_sum > target {
            false
        } else {
            greedy_partition(a, target, pos + 1, new_sum, count, g)
        }
    }
}

proof fn lemma_greedy_count_le_g(a: Seq<i64>, target: int, pos: int, seg_sum: int, count: int, g: int)
    requires
        0 <= pos <= a.len(),
        greedy_partition(a, target, pos, seg_sum, count, g) == true,
    ensures
        count <= g,
    decreases a.len() - pos,
{
    if pos < a.len() {
        let new_sum = seg_sum + a[pos] as int;
        if new_sum == target {
            lemma_greedy_count_le_g(a, target, pos + 1, 0, count + 1, g);
        } else if new_sum > target {
        } else {
            lemma_greedy_count_le_g(a, target, pos + 1, new_sum, count, g);
        }
    }
}

proof fn lemma_greedy_segment(a: Seq<i64>, target: int, s: int, e: int, pos: int, count: int, g: int)
    requires
        0 <= s <= pos < e <= a.len(),
        target == sum_range(a, s, e),
        forall|i: int| s <= i < a.len() ==> a[i] >= 1,
    ensures
        greedy_partition(a, target, pos, sum_range(a, s, pos), count, g)
            == greedy_partition(a, target, e, 0, count + 1, g),
    decreases e - pos,
{
    let seg_sum = sum_range(a, s, pos);
    lemma_sum_range_additive(a, s, pos, pos + 1);
    if pos + 1 == e {
        assert(sum_range(a, s, pos + 1) == sum_range(a, s, e));
        assert(seg_sum + a[pos] as int == target);
    } else {
        lemma_sum_range_mono_strict(a, s, pos + 1, e);
        assert((seg_sum + a[pos] as int) < target);
        lemma_greedy_segment(a, target, s, e, pos + 1, count, g);
        assert(sum_range(a, s, pos + 1) == seg_sum + a[pos] as int);
    }
}

proof fn lemma_greedy_from_witness(a: Seq<i64>, target: int, g: int, splits2: Seq<int>, count: int)
    requires
        0 <= count <= g,
        splits2.len() == g + 1,
        splits2[0] == 0,
        splits2[g] == a.len(),
        forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 1,
    ensures
        greedy_partition(a, target, splits2[count], 0, count, g) == true,
    decreases g - count,
{
    lemma_seq_mono_le(splits2, g, 0, count);
    lemma_seq_mono_le(splits2, g, count, g);
    assert(0 <= splits2[count] <= a.len());
    if count == g {
        assert(splits2[count] == a.len());
    } else {
        lemma_greedy_from_witness(a, target, g, splits2, count + 1);
        assert(splits2[count] < splits2[count + 1]);
        assert(sum_range(a, splits2[count], splits2[count + 1]) == target);
        lemma_seq_mono_le(splits2, g, count + 1, g);
        assert(splits2[count + 1] <= a.len());
        lemma_greedy_segment(a, target, splits2[count], splits2[count + 1], splits2[count], count, g);
        assert(sum_range(a, splits2[count], splits2[count]) == 0);
    }
}

proof fn lemma_greedy_sound(a: Seq<i64>, target: int, pos: int, count: int, g: int, prefix: Seq<int>)
    requires
        0 <= pos <= a.len(),
        0 <= count <= g,
        prefix.len() == count + 1,
        prefix[0] == 0,
        forall|j: int| 0 <= j < count ==> prefix[j] < #[trigger] prefix[j + 1] && sum_range(a, prefix[j], prefix[j + 1]) == target,
        prefix[count] <= pos,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 1,
        greedy_partition(a, target, pos, sum_range(a, prefix[count], pos), count, g) == true,
    ensures
        exists|splits2: Seq<int>|
            splits2.len() == g + 1 && splits2[0] == 0 && splits2[g] == a.len()
                && (forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target),
    decreases a.len() - pos,
{
    lemma_seq_mono_le(prefix, count, 0, count);
    assert(0 <= prefix[count]);
    let seg_sum = sum_range(a, prefix[count], pos);
    if pos >= a.len() {
        assert(seg_sum == 0 && count == g);
        lemma_sum_range_zero_implies_eq(a, prefix[count], pos);
        assert(prefix[count] == pos);
        assert(prefix[g] == a.len());
        assert(exists|splits2: Seq<int>|
            splits2.len() == g + 1 && splits2[0] == 0 && splits2[g] == a.len()
                && (forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target)) by {
            assert(prefix.len() == g + 1);
            assert(prefix[0] == 0);
            assert(prefix[g] == a.len());
            assert(forall|j: int| 0 <= j < g ==> prefix[j] < #[trigger] prefix[j + 1] && sum_range(a, prefix[j], prefix[j + 1]) == target);
        };
    } else {
        lemma_sum_range_additive(a, prefix[count], pos, pos + 1);
        let new_sum = seg_sum + a[pos] as int;
        if new_sum == target {
            let prefix2 = prefix.push(pos + 1);
            assert(prefix2.len() == count + 2);
            assert(prefix2[count] == prefix[count]);
            assert(prefix2[count + 1] == pos + 1);
            assert forall|j: int| 0 <= j < count + 1 implies prefix2[j] < #[trigger] prefix2[j + 1] && sum_range(a, prefix2[j], prefix2[j + 1]) == target by {
                if j < count {
                    assert(prefix2[j] == prefix[j]);
                    assert(prefix2[j + 1] == prefix[j + 1]);
                } else {
                    assert(j == count);
                    assert(prefix2[count] == prefix[count]);
                    assert(prefix2[count + 1] == pos + 1);
                    assert(prefix[count] <= pos);
                    assert(sum_range(a, prefix[count], pos + 1) == new_sum);
                }
            };
            lemma_greedy_count_le_g(a, target, pos + 1, 0, count + 1, g);
            lemma_greedy_sound(a, target, pos + 1, count + 1, g, prefix2);
        } else if new_sum > target {
            assert(false);
        } else {
            lemma_greedy_sound(a, target, pos + 1, count, g, prefix);
        }
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

proof fn lemma_mul_step(cnt: int, tgt: int, x: int, y: int, z: int)
    requires
        cnt >= 1,
        x == y + z,
        y == (cnt - 1) * tgt,
        z == tgt,
    ensures
        x == cnt * tgt,
{
    assert(x == cnt * tgt) by (nonlinear_arith)
        requires
            x == y + z,
            y == (cnt - 1) * tgt,
            z == tgt;
}

proof fn lemma_witness_total(a: Seq<i64>, g: int, target: int, splits2: Seq<int>, count: int)
    requires
        0 <= count <= g,
        splits2.len() == g + 1,
        splits2[0] == 0,
        splits2[g] <= a.len(),
        forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target,
    ensures
        sum_range(a, 0, splits2[count]) == count * target,
    decreases count,
{
    lemma_seq_mono_le(splits2, g, 0, count);
    lemma_seq_mono_le(splits2, g, count, g);
    if count > 0 {
        lemma_witness_total(a, g, target, splits2, count - 1);
        lemma_seq_mono_le(splits2, g, 0, count - 1);
        lemma_seq_mono_le(splits2, g, count - 1, count);
        lemma_seq_mono_le(splits2, g, count, g);
        lemma_sum_range_additive(a, 0, splits2[count - 1], splits2[count]);
        let jj = count - 1;
        assert(0 <= jj < g);
        assert(splits2[jj] < splits2[jj + 1] && sum_range(a, splits2[jj], splits2[jj + 1]) == target);
        assert(splits2[count - 1] < splits2[count]);
        assert(sum_range(a, splits2[count - 1], splits2[count]) == target);
        assert(sum_range(a, 0, splits2[count - 1]) == (count - 1) * target);
        lemma_mul_step(
            count,
            target,
            sum_range(a, 0, splits2[count]),
            sum_range(a, 0, splits2[count - 1]),
            sum_range(a, splits2[count - 1], splits2[count]),
        );
        assert(sum_range(a, 0, splits2[count]) == count * target);
    } else {
        assert(count == 0);
        assert(splits2[count] == 0);
        assert(sum_range(a, 0, splits2[count]) == 0);
        assert(count * target == 0);
    }
}

proof fn lemma_greedy_iff_can_partition(a: Seq<i64>, n: usize, g: int, target: int)
    requires
        a.len() == n as int,
        1 <= g <= n as int,
        target == sum_range(a, 0, n as int) / g,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 1,
    ensures
        greedy_partition(a, target, 0, 0, 0, g) == can_partition_k(a, n, g),
{
    if greedy_partition(a, target, 0, 0, 0, g) {
        let prefix: Seq<int> = seq![0int];
        assert(prefix[0] == 0);
        assert(sum_range(a, prefix[0], 0) == 0);
        lemma_greedy_sound(a, target, 0, 0, g, prefix);
        assert(exists|splits2: Seq<int>|
            splits2.len() == g + 1 && splits2[0] == 0 && splits2[g] == a.len()
                && (forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target));
        let splits2 = choose|splits2: Seq<int>|
            splits2.len() == g + 1 && splits2[0] == 0 && splits2[g] == a.len()
                && (forall|j: int| 0 <= j < g ==> splits2[j] < #[trigger] splits2[j + 1] && sum_range(a, splits2[j], splits2[j + 1]) == target);
        lemma_witness_total(a, g, target, splits2, g);
        assert(sum_range(a, 0, splits2[g]) == g * target);
        assert(sum_range(a, 0, n as int) == g * target);
        assert(sum_range(a, 0, n as int) % g == 0) by (nonlinear_arith)
            requires sum_range(a, 0, n as int) == g * target, g >= 1;
        assert(sum_range(a, 0, n as int) / g == target) by (nonlinear_arith)
            requires sum_range(a, 0, n as int) == g * target, g >= 1;
    }
    if can_partition_k(a, n, g) {
        assert(sum_range(a, 0, n as int) % g == 0);
        let target2 = sum_range(a, 0, n as int) / g;
        assert(target2 == target);
        assert(exists|splits: Seq<int>|
            splits.len() == g + 1 &&
            splits[0] == 0 && splits[g] == n &&
            (forall|j: int| 0 <= j && j < g ==>
                splits[j] < splits[j + 1] &&
                sum_range(a, splits[j], #[trigger] splits[j + 1]) == target2));
        let splits2 = choose|splits: Seq<int>|
            splits.len() == g + 1 &&
            splits[0] == 0 && splits[g] == n &&
            (forall|j: int| 0 <= j && j < g ==>
                splits[j] < splits[j + 1] &&
                sum_range(a, splits[j], #[trigger] splits[j + 1]) == target2);
        assert(splits2[g] == n as int);
        lemma_greedy_from_witness(a, target, g, splits2, 0);
        assert(splits2[0] == 0);
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
            ok == can_partition_k(a@, n, g as int),
    {
        let target = total / (g as i64);
        proof {
            lemma_sum_range_pos_strict(a@, 0, n as int);
            assert(total as int >= n as int);
            assert(n as int >= g as int);
            assert(total as int >= g as int);
            assert(target as int >= 1) by (nonlinear_arith)
                requires
                    total as int >= g as int,
                    g as int >= 1,
                    target as int == total as int / (g as int);
        }
        let mut seg_sum: i64 = 0;
        let mut count: usize = 0;
        let mut j: usize = 0;
        let mut ok = true;
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
                ok ==> greedy_partition(a@, target as int, j as int, seg_sum as int, count as int, g as int)
                    == greedy_partition(a@, target as int, 0, 0, 0, g as int),
                !ok ==> !greedy_partition(a@, target as int, 0, 0, 0, g as int),
            decreases n - j
        {
            let old_ok = ok;
            let old_seg_sum = seg_sum;
            let old_count = count;
            let old_j = j;
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
            proof {
                if old_ok {
                    let new_sum = old_seg_sum as int + a@[old_j as int] as int;
                    assert(greedy_partition(a@, target as int, old_j as int, old_seg_sum as int, old_count as int, g as int)
                        == greedy_partition(a@, target as int, 0, 0, 0, g as int));
                    if new_sum == target as int {
                        assert(greedy_partition(a@, target as int, old_j as int, old_seg_sum as int, old_count as int, g as int)
                            == greedy_partition(a@, target as int, old_j as int + 1, 0, old_count as int + 1, g as int));
                        assert(ok);
                        assert(count as int == old_count as int + 1);
                        assert(seg_sum == 0);
                        assert(j as int == old_j as int + 1);
                    } else if new_sum > target as int {
                        assert(greedy_partition(a@, target as int, old_j as int, old_seg_sum as int, old_count as int, g as int)
                            == false);
                        assert(!ok);
                    } else {
                        assert(greedy_partition(a@, target as int, old_j as int, old_seg_sum as int, old_count as int, g as int)
                            == greedy_partition(a@, target as int, old_j as int + 1, new_sum, old_count as int, g as int));
                        assert(ok);
                        assert(seg_sum as int == new_sum);
                        assert(count as int == old_count as int);
                        assert(j as int == old_j as int + 1);
                    }
                } else {
                    assert(!ok);
                }
            }
        }
        proof {
            assert((ok && count == g && seg_sum == 0) == greedy_partition(a@, target as int, 0, 0, 0, g as int)) by {
                if ok {
                    assert(greedy_partition(a@, target as int, n as int, seg_sum as int, count as int, g as int)
                        == greedy_partition(a@, target as int, 0, 0, 0, g as int));
                    assert(greedy_partition(a@, target as int, n as int, seg_sum as int, count as int, g as int)
                        == (seg_sum as int == 0 && count as int == g as int));
                }
            };
            lemma_greedy_iff_can_partition(a@, n, g as int, target as int);
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
            forall|k2: int| (n as int - ans as int) < k2 && k2 <= n as int ==> !can_partition_k(a@, n, k2),
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
                forall|k2: int| (g as int) < k2 && k2 <= (n as int) ==> !can_partition_k(a@, n, k2),
            decreases g,
        {
            proof {
                lemma_sum_range_pos_strict(a@, 0, n as int);
            }
            if total % (g as i64) == 0 && total >= g as i64 {
                let ok = Solution::check_partition(n, &a, g, total);
                if ok {
                    best_k = g;
                    proof {
                        assert(can_partition_k(a@, n, g as int));
                        assert(forall|k2: int| (g as int) < k2 && k2 <= (n as int) ==> !can_partition_k(a@, n, k2));
                    }
                    return (n as i64) - (best_k as i64);
                } else {
                    proof {
                        assert(!can_partition_k(a@, n, g as int));
                    }
                }
            } else {
                proof {
                    if total % (g as i64) != 0 {
                        assert(sum_range(a@, 0, n as int) % (g as int) != 0);
                        assert(!can_partition_k(a@, n, g as int));
                    } else {
                        assert(total < g as i64);
                        assert(false);
                    }
                }
            }
            g -= 1;
        }
        proof {
            assert(g == 0);
            assert(can_partition_k(a@, n, 1));
            assert((g as int) < 1 && 1 <= (n as int));
            assert(!can_partition_k(a@, n, 1));
            assert(false);
        }
        (n as i64) - (best_k as i64)
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

}
