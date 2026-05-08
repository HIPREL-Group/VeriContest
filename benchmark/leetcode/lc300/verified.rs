use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_lis_subseq(nums: Seq<i32>, idx_seq: Seq<int>) -> bool {
    idx_seq.len() >= 1
    && forall |j: int| 0 <= j < idx_seq.len() ==> 0 <= (#[trigger] idx_seq[j]) < nums.len()
    && forall |j: int| 0 <= j < idx_seq.len() - 1 ==>
        idx_seq[j] < idx_seq[j + 1] && (#[trigger] nums[idx_seq[j]]) < nums[idx_seq[j + 1]]
}

pub open spec fn has_lis_of_length(nums: Seq<i32>, k: int) -> bool {
    exists |idx_seq: Seq<int>|
        idx_seq.len() == k && (#[trigger] is_lis_subseq(nums, idx_seq))
}

spec fn max_lis_before(nums: Seq<i32>, i: int, bound: i32) -> nat
    decreases i, 0nat,
{
    if i <= 0 {
        0
    } else {
        let rest = max_lis_before(nums, i - 1, bound);
        if nums[i - 1] < bound {
            let cur = lis_ending_at(nums, i - 1);
            if cur > rest { cur } else { rest }
        } else {
            rest
        }
    }
}

spec fn lis_ending_at(nums: Seq<i32>, i: int) -> nat
    decreases i, 1nat,
{
    if i < 0 {
        0
    } else {
        1 + max_lis_before(nums, i, nums[i])
    }
}

spec fn max_lis_range(nums: Seq<i32>, end: int) -> nat
    decreases end,
{
    if end <= 0 {
        0
    } else {
        let prev = max_lis_range(nums, end - 1);
        let cur = lis_ending_at(nums, end - 1);
        if cur > prev { cur } else { prev }
    }
}

proof fn lemma_lis_ending_at_pos(nums: Seq<i32>, i: int)
    requires 0 <= i < nums.len(),
    ensures lis_ending_at(nums, i) >= 1,
{
}

proof fn lemma_lis_ending_at_bound(nums: Seq<i32>, i: int)
    requires 0 <= i < nums.len(),
    ensures lis_ending_at(nums, i) <= (i + 1) as nat,
    decreases i, 1nat,
{
    if i > 0 {
        lemma_max_lis_before_bound(nums, i, nums[i]);
    }
}

proof fn lemma_max_lis_before_bound(nums: Seq<i32>, i: int, bound: i32)
    requires 0 <= i <= nums.len(),
    ensures max_lis_before(nums, i, bound) <= i as nat,
    decreases i, 0nat,
{
    if i > 0 {
        lemma_max_lis_before_bound(nums, i - 1, bound);
        if nums[i - 1] < bound {
            lemma_lis_ending_at_bound(nums, i - 1);
        }
    }
}

proof fn lemma_max_lis_range_bound(nums: Seq<i32>, end: int)
    requires 0 < end <= nums.len(),
    ensures max_lis_range(nums, end) >= 1,
            max_lis_range(nums, end) <= end as nat,
    decreases end,
{
    lemma_lis_ending_at_pos(nums, end - 1);
    lemma_lis_ending_at_bound(nums, end - 1);
    if end > 1 {
        lemma_max_lis_range_bound(nums, end - 1);
    }
}

proof fn lemma_single_lis(nums: Seq<i32>, i: int)
    requires 0 <= i < nums.len(),
    ensures has_lis_of_length(nums, 1),
{
    let w: Seq<int> = seq![i];
    assert(w.len() == 1);
    assert(w[0] == i);
    assert(is_lis_subseq(nums, w));
}

proof fn lemma_extend_lis(nums: Seq<i32>, idx_seq: Seq<int>, new_idx: int)
    requires
        is_lis_subseq(nums, idx_seq),
        0 <= new_idx < nums.len(),
        idx_seq[idx_seq.len() - 1] < new_idx,
        nums[idx_seq[idx_seq.len() - 1]] < nums[new_idx],
    ensures
        is_lis_subseq(nums, idx_seq.push(new_idx)),
{
    let ext = idx_seq.push(new_idx);
    assert(ext.len() >= 1);
    assert forall |j: int| 0 <= j < ext.len() implies
        0 <= (#[trigger] ext[j]) < nums.len() by {
        if j < idx_seq.len() {
            assert(ext[j] == idx_seq[j]);
        } else {
            assert(ext[j] == new_idx);
        }
    }
    assert forall |j: int| 0 <= j < ext.len() - 1 implies
        (#[trigger] ext[j]) < ext[j + 1] by {
        if j < idx_seq.len() - 1 {
            assert(ext[j] == idx_seq[j]);
            assert(ext[j + 1] == idx_seq[j + 1]);
            assert(nums[idx_seq[j]] < nums[idx_seq[j + 1]]);
        } else {
            assert(ext[j] == idx_seq[idx_seq.len() - 1]);
            assert(ext[j + 1] == new_idx);
        }
    }
    assert forall |j: int| 0 <= j < ext.len() - 1 implies
        (#[trigger] nums[ext[j]]) < nums[ext[j + 1]] by {
        if j < idx_seq.len() - 1 {
            assert(ext[j] == idx_seq[j]);
            assert(ext[j + 1] == idx_seq[j + 1]);
            assert(nums[idx_seq[j]] < nums[idx_seq[j + 1]]);
        } else {
            assert(ext[j] == idx_seq[idx_seq.len() - 1]);
            assert(ext[j + 1] == new_idx);
        }
    }
    assert forall |j: int| 0 <= j < ext.len() - 1 implies
        ext[j] < ext[j + 1] && (#[trigger] nums[ext[j]]) < nums[ext[j + 1]] by {
        assert(ext[j] < ext[j + 1]);
        assert(nums[ext[j]] < nums[ext[j + 1]]);
    }
}

proof fn lemma_max_lis_before_witness(nums: Seq<i32>, i: int, bound: i32) -> (j: int)
    requires
        0 <= i <= nums.len(),
        max_lis_before(nums, i, bound) > 0,
    ensures
        0 <= j < i,
        j < nums.len(),
        nums[j] < bound,
        lis_ending_at(nums, j) == max_lis_before(nums, i, bound),
    decreases i, 0nat,
{
    if i <= 0 {
        0 
    } else {
        let rest = max_lis_before(nums, i - 1, bound);
        if nums[i - 1] < bound {
            let cur = lis_ending_at(nums, i - 1);
            if cur > rest {
                i - 1
            } else if rest > 0 {
                lemma_max_lis_before_witness(nums, i - 1, bound)
            } else {
                i - 1
            }
        } else {
            lemma_max_lis_before_witness(nums, i - 1, bound)
        }
    }
}

proof fn lemma_has_lis_ending_at(nums: Seq<i32>, i: int) -> (w: Seq<int>)
    requires 0 <= i < nums.len(),
    ensures
        has_lis_of_length(nums, lis_ending_at(nums, i) as int),
        w.len() == lis_ending_at(nums, i) as int,
        is_lis_subseq(nums, w),
        w[w.len() - 1] == i,
    decreases i, 1nat,
{
    let mlb = max_lis_before(nums, i, nums[i]);
    if mlb == 0 {
        let w: Seq<int> = seq![i];
        assert(is_lis_subseq(nums, w));
        w
    } else {
        let j = lemma_max_lis_before_witness(nums, i, nums[i]);
        let prev_w = lemma_has_lis_ending_at(nums, j);
        lemma_extend_lis(nums, prev_w, i);
        let w = prev_w.push(i);
        assert(w.len() as int == (mlb + 1) as int);
        assert(w.len() as int == lis_ending_at(nums, i) as int);
        w
    }
}

proof fn lemma_max_lis_is_lis(nums: Seq<i32>, n: int)
    requires 0 < n <= nums.len(),
    ensures has_lis_of_length(nums, max_lis_range(nums, n) as int),
    decreases n,
{
    let cur = lis_ending_at(nums, n - 1);
    let _ = lemma_has_lis_ending_at(nums, n - 1);
    if n > 1 {
        let prev = max_lis_range(nums, n - 1);
        if prev >= cur {
            lemma_max_lis_is_lis(nums, n - 1);
        }
    }
}

proof fn lemma_lis_upper_bound(nums: Seq<i32>, idx_seq: Seq<int>, i: int)
    requires
        is_lis_subseq(nums, idx_seq),
        idx_seq.len() >= 1,
        idx_seq[idx_seq.len() - 1] == i,
        0 <= i < nums.len(),
    ensures
        idx_seq.len() <= lis_ending_at(nums, i) as int,
    decreases idx_seq.len(),
{
    if idx_seq.len() == 1 {
        lemma_lis_ending_at_pos(nums, i);
    } else {
        let prev_len = idx_seq.len() - 1;
        let prev_idx = idx_seq[prev_len - 1];
        let prev_seq = idx_seq.subrange(0, prev_len as int);

        assert(prev_seq.len() == prev_len);
        assert forall |j: int| 0 <= j < prev_seq.len() implies
            0 <= (#[trigger] prev_seq[j]) < nums.len() by {
            assert(prev_seq[j] == idx_seq[j]);
            assert(0 <= idx_seq[j] < nums.len());
        }
        assert forall |j: int| 0 <= j < prev_seq.len() - 1 implies
            (#[trigger] prev_seq[j]) < prev_seq[j + 1] by {
            assert(prev_seq[j] == idx_seq[j]);
            assert(prev_seq[j + 1] == idx_seq[j + 1]);
            assert(nums[idx_seq[j]] < nums[idx_seq[j + 1]]);
        }
        assert forall |j: int| 0 <= j < prev_seq.len() - 1 implies
            (#[trigger] nums[prev_seq[j]]) < nums[prev_seq[j + 1]] by {
            assert(prev_seq[j] == idx_seq[j]);
            assert(prev_seq[j + 1] == idx_seq[j + 1]);
            assert(nums[idx_seq[j]] < nums[idx_seq[j + 1]]);
        }
        assert forall |j: int| 0 <= j < prev_seq.len() - 1 implies
            prev_seq[j] < prev_seq[j + 1] && (#[trigger] nums[prev_seq[j]]) < nums[prev_seq[j + 1]] by {
            assert(prev_seq[j] < prev_seq[j + 1]);
            assert(nums[prev_seq[j]] < nums[prev_seq[j + 1]]);
        }
        assert(is_lis_subseq(nums, prev_seq));

        assert(nums[idx_seq[prev_len - 1]] < nums[idx_seq[prev_len]]);
        assert(idx_seq[prev_len - 1] < idx_seq[prev_len]);
        assert(prev_idx < i);
        assert(nums[prev_idx] < nums[i]);

        lemma_lis_upper_bound(nums, prev_seq, prev_idx);
        lemma_max_lis_before_includes(nums, i, nums[i], prev_idx);
    }
}

proof fn lemma_max_lis_before_includes(nums: Seq<i32>, i: int, bound: i32, j: int)
    requires
        0 <= j < i,
        j < nums.len(),
        nums[j] < bound,
    ensures
        max_lis_before(nums, i, bound) >= lis_ending_at(nums, j),
    decreases i, 0nat,
{
    if i == j + 1 {
    } else {
        lemma_max_lis_before_includes(nums, i - 1, bound, j);
    }
}

proof fn lemma_max_lis_range_includes(nums: Seq<i32>, end: int, i: int)
    requires
        0 <= i < end,
        end <= nums.len(),
    ensures
        max_lis_range(nums, end) >= lis_ending_at(nums, i),
    decreases end,
{
    if i == end - 1 {
    } else {
        lemma_max_lis_range_includes(nums, end - 1, i);
    }
}

proof fn lemma_no_longer_lis(nums: Seq<i32>, k: int)
    requires
        nums.len() > 0,
        k > max_lis_range(nums, nums.len() as int) as int,
    ensures
        !has_lis_of_length(nums, k),
{
    if has_lis_of_length(nums, k) {
        let idx_seq = choose |idx_seq: Seq<int>|
            idx_seq.len() == k && (#[trigger] is_lis_subseq(nums, idx_seq));
        let last = idx_seq[idx_seq.len() - 1];
        assert(0 <= last < nums.len());
        lemma_lis_upper_bound(nums, idx_seq, last);
        lemma_max_lis_range_includes(nums, nums.len() as int, last);
    }
}

impl Solution {
    pub fn length_of_lis(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 2500,
            forall |i: int| 0 <= i < nums.len() ==> -10_000 <= (#[trigger] nums[i]) <= 10_000,
        ensures
            res >= 1,
            res <= nums.len() as int,
            has_lis_of_length(nums@, res as int),
            forall |k: int| k > res as int ==> !has_lis_of_length(nums@, k),
    {
        let n = nums.len();
        let mut dp: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 2500,
                n == nums.len(),
                0 <= i <= n,
                dp.len() == i,
                forall |j: int| 0 <= j < i ==> (#[trigger] dp[j]) == 1i32,
            decreases n - i,
        {
            dp.push(1i32);
            i += 1;
        }
        proof {
            lemma_lis_ending_at_pos(nums@, 0);
            assert(lis_ending_at(nums@, 0) == 1nat);
        }
        i = 1;
        while i < n
            invariant
                1 <= n <= 2500,
                n == nums.len(),
                dp.len() == n,
                1 <= i <= n,
                forall |j: int| 0 <= j < i ==> (#[trigger] dp[j]) as nat == lis_ending_at(nums@, j),
                forall |j: int| 0 <= j < i ==> 1 <= (#[trigger] dp[j]) <= (j + 1) as i32,
                forall |j: int| i <= j < n ==> (#[trigger] dp[j]) == 1i32,
                forall |ii: int| 0 <= ii < nums.len() ==> -10_000 <= (#[trigger] nums[ii]) <= 10_000,
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < i
                invariant
                    1 <= n <= 2500,
                    n == nums.len(),
                    dp.len() == n,
                    1 <= i < n,
                    0 <= j <= i,
                    forall |k: int| 0 <= k < i ==> (#[trigger] dp[k]) as nat == lis_ending_at(nums@, k),
                    forall |k: int| 0 <= k < i ==> 1 <= (#[trigger] dp[k]) <= (k + 1) as i32,
                    forall |k: int| i < k < n ==> (#[trigger] dp[k]) == 1i32,
                    dp[i as int] as int == 1 + max_lis_before(nums@, j as int, nums@[i as int]) as int,
                    1 <= dp[i as int] <= (i + 1) as i32,
                    forall |ii: int| 0 <= ii < nums.len() ==> -10_000 <= (#[trigger] nums[ii]) <= 10_000,
                decreases i - j,
            {
                if nums[j] < nums[i] {
                    if dp[j] + 1 > dp[i] {
                        dp[i] = dp[j] + 1;
                    }
                }
                j += 1;
            }
            proof {
                assert(dp[i as int] as int == 1 + max_lis_before(nums@, i as int, nums@[i as int]) as int);
                assert(lis_ending_at(nums@, i as int) == (1 + max_lis_before(nums@, i as int, nums@[i as int])) as nat);
                lemma_lis_ending_at_bound(nums@, i as int);
            }
            i += 1;
        }
        let mut best = dp[0];
        proof {
            assert(dp[0] as nat == lis_ending_at(nums@, 0));
            lemma_lis_ending_at_pos(nums@, 0);
            assert(max_lis_range(nums@, 0) == 0nat);
            let cur = lis_ending_at(nums@, 0);
            assert(cur >= 1);
        }
        let mut k: usize = 1;
        while k < n
            invariant
                1 <= n <= 2500,
                n == nums.len(),
                dp.len() == n,
                1 <= k <= n,
                forall |j: int| 0 <= j < n ==> (#[trigger] dp[j]) as nat == lis_ending_at(nums@, j),
                forall |j: int| 0 <= j < n ==> 1 <= (#[trigger] dp[j]) <= (j + 1) as i32,
                best as nat == max_lis_range(nums@, k as int),
                1 <= best <= n as i32,
            decreases n - k,
        {
            if dp[k] > best {
                best = dp[k];
            }
            k += 1;
        }
        proof {
            lemma_max_lis_is_lis(nums@, n as int);
            lemma_max_lis_range_bound(nums@, n as int);
            assert forall |kk: int| kk > best as int implies !has_lis_of_length(nums@, kk) by {
                lemma_no_longer_lis(nums@, kk);
            }
        }
        best
    }
}

}
