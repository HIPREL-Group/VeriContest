use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(x: nat) -> nat
        decreases x,
    {
        if x == 0 {
            0
        } else {
            (x % 10) + Self::digit_sum_spec(x / 10)
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int) -> bool {
        0 <= i < j < nums.len()
            && Self::digit_sum_spec(nums[i] as nat) == Self::digit_sum_spec(nums[j] as nat)
    }
}

pub open spec fn max_with_digitsum_before(nums: Seq<i32>, ds: nat, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else {
        let prev = max_with_digitsum_before(nums, ds, end - 1);
        if Solution::digit_sum_spec(nums[end - 1] as nat) == ds {
            if prev == -1 || nums[end - 1] as int > prev { nums[end - 1] as int } else { prev }
        } else {
            prev
        }
    }
}

pub open spec fn best_sum_upto(nums: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        -1
    } else {
        let prev_best = best_sum_upto(nums, end - 1);
        let mx = max_with_digitsum_before(nums, Solution::digit_sum_spec(nums[end - 1] as nat), end - 1);
        let cand = if mx == -1 { -1 } else { mx + nums[end - 1] as int };
        if cand == -1 {
            prev_best
        } else if prev_best == -1 || cand > prev_best {
            cand
        } else {
            prev_best
        }
    }
}

proof fn lemma_max_with_digitsum_char(nums: Seq<i32>, ds: nat, end: int)
    requires 0 <= end <= nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        max_with_digitsum_before(nums, ds, end) == -1 ==>
            (forall |k: int| 0 <= k < end ==> Solution::digit_sum_spec(#[trigger] nums[k] as nat) != ds),
        (forall |k: int| 0 <= k < end ==> Solution::digit_sum_spec(#[trigger] nums[k] as nat) != ds) ==>
            max_with_digitsum_before(nums, ds, end) == -1,
        max_with_digitsum_before(nums, ds, end) != -1 ==> (
            exists |k: int| 0 <= k < end
                && Solution::digit_sum_spec(nums[k] as nat) == ds
                && nums[k] as int == max_with_digitsum_before(nums, ds, end)
        ),
        max_with_digitsum_before(nums, ds, end) != -1 ==> (
            forall |k: int| 0 <= k < end && Solution::digit_sum_spec(#[trigger] nums[k] as nat) == ds
                ==> nums[k] as int <= max_with_digitsum_before(nums, ds, end)
        ),
    decreases end
{
    if end > 0 {
        lemma_max_with_digitsum_char(nums, ds, end - 1);
    }
}

proof fn lemma_best_sum_char(nums: Seq<i32>, end: int)
    requires 0 <= end <= nums.len(),
        forall |k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 1,
    ensures
        best_sum_upto(nums, end) == -1 ==>
            (forall |i: int, j: int| 0 <= i < j < end ==> !Solution::valid_pair(nums, i, j)),
        (forall |i: int, j: int| 0 <= i < j < end ==> !Solution::valid_pair(nums, i, j)) ==>
            best_sum_upto(nums, end) == -1,
        best_sum_upto(nums, end) != -1 ==> (
            exists |i: int, j: int| 0 <= i < j < end && Solution::valid_pair(nums, i, j)
                && best_sum_upto(nums, end) == nums[i] as int + nums[j] as int
        ),
        best_sum_upto(nums, end) != -1 ==> (
            forall |i: int, j: int| 0 <= i < j < end && #[trigger] Solution::valid_pair(nums, i, j)
                ==> nums[i] as int + nums[j] as int <= best_sum_upto(nums, end)
        ),
    decreases end
{
    if end > 0 {
        lemma_best_sum_char(nums, end - 1);
        let ds = Solution::digit_sum_spec(nums[end - 1] as nat);
        lemma_max_with_digitsum_char(nums, ds, end - 1);
        let prev_best = best_sum_upto(nums, end - 1);
        let mx = max_with_digitsum_before(nums, ds, end - 1);
        let cand = if mx == -1 { -1int } else { mx + nums[end - 1] as int };
        assert(!Solution::valid_pair(nums, end - 1, end - 1));
        assert forall |i: int| 0 <= i < end - 1 && Solution::digit_sum_spec(#[trigger] nums[i] as nat) == ds
            implies nums[i] as int <= (if mx == -1 { -1int } else { mx }) by {
            if mx != -1 {
                lemma_max_with_digitsum_char(nums, ds, end - 1);
            }
        }
        if mx == -1 {
            assert(forall |k: int| 0 <= k < end - 1 ==> #[trigger] Solution::digit_sum_spec(nums[k] as nat) != ds);
        } else {
            assert(exists |k: int| 0 <= k < end - 1
                && Solution::digit_sum_spec(nums[k] as nat) == ds
                && nums[k] as int == mx);
        }
        if best_sum_upto(nums, end) == -1 {
            assert(cand == -1);
            assert(prev_best == -1);
            assert(mx == -1);
            assert forall |i: int, j: int| 0 <= i < j < end implies !Solution::valid_pair(nums, i, j) by {
                if j < end - 1 {
                } else {
                    assert(j == end - 1);
                    if Solution::valid_pair(nums, i, j) {
                        assert(Solution::digit_sum_spec(nums[i] as nat) == ds);
                    }
                }
            }
        }
        if best_sum_upto(nums, end) != -1 {
            if cand == -1 || (prev_best != -1 && !(cand > prev_best)) {
                assert(best_sum_upto(nums, end) == prev_best);
            } else {
                assert(best_sum_upto(nums, end) == cand);
                assert(mx != -1);
                let k = choose |k: int| 0 <= k < end - 1
                    && Solution::digit_sum_spec(nums[k] as nat) == ds
                    && nums[k] as int == mx;
                assert(Solution::valid_pair(nums, k, end - 1));
                assert(best_sum_upto(nums, end) == nums[k] as int + nums[end - 1] as int);
            }
            assert forall |i: int, j: int| 0 <= i < j < end && #[trigger] Solution::valid_pair(nums, i, j)
                implies nums[i] as int + nums[j] as int <= best_sum_upto(nums, end) by {
                if j < end - 1 {
                    assert(nums[i] as int + nums[j] as int <= prev_best);
                } else {
                    assert(j == end - 1);
                    assert(Solution::digit_sum_spec(nums[i] as nat) == ds);
                    assert(nums[i] as int <= mx);
                }
            }
        }
    }
}

pub open spec fn pow10(k: nat) -> nat
    decreases k
{
    if k == 0 { 1 } else { 10 * pow10((k - 1) as nat) }
}

proof fn lemma_digit_sum_spec_bound_aux(x: nat, budget: nat)
    requires x < pow10(budget),
    ensures Solution::digit_sum_spec(x) <= 9 * budget,
    decreases x
{
    if x > 0 {
        if budget == 0 {
            assert(pow10(0) == 1);
        }
        assert(budget >= 1);
        assert(pow10(budget) == 10 * pow10((budget - 1) as nat));
        assert(x / 10 < pow10((budget - 1) as nat)) by (nonlinear_arith)
            requires x < 10 * pow10((budget - 1) as nat), x == 10 * (x / 10) + x % 10, 0 <= x % 10 < 10;
        lemma_digit_sum_spec_bound_aux(x / 10, (budget - 1) as nat);
        assert(Solution::digit_sum_spec(x) == (x % 10) + Solution::digit_sum_spec(x / 10));
        assert(9 * ((budget - 1) as nat) + 9 == 9 * budget) by (nonlinear_arith)
            requires budget >= 1;
    }
}

proof fn lemma_digit_sum_spec_bound(x: nat)
    requires x <= 1_000_000_000,
    ensures Solution::digit_sum_spec(x) <= 90,
{
    assert(pow10(10) == 10_000_000_000) by {
        assert(pow10(0) == 1);
        assert(pow10(1) == 10);
        assert(pow10(2) == 100);
        assert(pow10(3) == 1_000);
        assert(pow10(4) == 10_000);
        assert(pow10(5) == 100_000);
        assert(pow10(6) == 1_000_000);
        assert(pow10(7) == 10_000_000);
        assert(pow10(8) == 100_000_000);
        assert(pow10(9) == 1_000_000_000);
        assert(pow10(10) == 10_000_000_000);
    }
    assert(x < pow10(10));
    lemma_digit_sum_spec_bound_aux(x, 10);
}

fn digit_sum_exec(x0: i32) -> (result: i64)
    requires 1 <= x0 <= 1_000_000_000,
    ensures result as nat == Solution::digit_sum_spec(x0 as nat),
        0 <= result <= 90,
{
    let mut x = x0;
    let mut s: i64 = 0;
    proof {
        lemma_digit_sum_spec_bound(x0 as nat);
    }
    while x > 0
        invariant
            0 <= x,
            s as nat + Solution::digit_sum_spec(x as nat) == Solution::digit_sum_spec(x0 as nat),
            Solution::digit_sum_spec(x0 as nat) <= 90,
            0 <= s <= 90,
        decreases x,
    {
        proof {
            assert(Solution::digit_sum_spec(x as nat) == (x as nat % 10) + Solution::digit_sum_spec(x as nat / 10));
            assert((x % 10) as nat == x as nat % 10);
            assert((x / 10) as nat == x as nat / 10);
        }
        s = s + (x % 10) as i64;
        x = x / 10;
    }
    proof {
        assert(Solution::digit_sum_spec(x as nat) == 0);
    }
    s
}

impl Solution {
    pub fn maximum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            -1 <= result as int <= 2000000000,
            result == -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() ==> !(#[trigger] Self::valid_pair(nums@, i, j)),
            result != -1 ==> exists |i: int, j: int|
                0 <= i < j < nums.len()
                && Self::valid_pair(nums@, i, j)
                && result as int == nums[i] as int + nums[j] as int,
            result != -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() && #[trigger] Self::valid_pair(nums@, i, j)
                ==> nums[i] as int + nums[j] as int <= result as int,
    {
        let n = nums.len();
        let mut max_bucket: Vec<i32> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 90
            invariant
                max_bucket@.len() == vi as int,
                0 <= vi <= 91,
                forall |v: int| 0 <= v < vi as int ==> #[trigger] max_bucket@[v] == max_with_digitsum_before(nums@, v as nat, 0),
            decreases 91 - vi,
        {
            max_bucket.push(-1);
            vi += 1;
        }

        let mut best: i32 = -1;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 100000,
                max_bucket@.len() == 91,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums@[k] <= 1_000_000_000,
                forall |v: int| 0 <= v <= 90 ==> #[trigger] max_bucket@[v] == max_with_digitsum_before(nums@, v as nat, i as int),
                best as int == best_sum_upto(nums@, i as int),
                -1 <= best <= 2_000_000_000,
            decreases n - i,
        {
            let ds = digit_sum_exec(nums[i]);
            let dsu = ds as usize;
            proof {
                assert(dsu <= 90);
                assert(ds as nat == Solution::digit_sum_spec(nums@[i as int] as nat));
            }
            let mx = max_bucket[dsu];
            proof {
                assert(mx as int == max_with_digitsum_before(nums@, dsu as nat, i as int));
                lemma_max_with_digitsum_char(nums@, dsu as nat, i as int);
                if mx != -1 {
                    assert(0 <= mx <= 1_000_000_000);
                }
            }
            if mx != -1 {
                let cand = nums[i] + mx;
                if best == -1 || cand > best {
                    best = cand;
                }
            }
            if mx == -1 || nums[i] > mx {
                max_bucket.set(dsu, nums[i]);
            }
            proof {
                assert forall |v: int| 0 <= v <= 90 && v != dsu as int implies
                    #[trigger] max_bucket@[v] == max_with_digitsum_before(nums@, v as nat, i as int + 1) by {
                    assert(Solution::digit_sum_spec(nums@[i as int] as nat) != v as nat);
                }
            }
            i += 1;
        }

        proof {
            lemma_best_sum_char(nums@, n as int);
        }
        best
    }
}

}
