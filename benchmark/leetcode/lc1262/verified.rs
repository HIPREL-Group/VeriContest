use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn subset_sum(nums: Seq<i32>, sel: Seq<bool>, hi: int) -> int
    decreases hi
{
    if hi <= 0 { 0 }
    else {
        (if sel[hi - 1] { nums[hi - 1] as int } else { 0 })
        + subset_sum(nums, sel, hi - 1)
    }
}


pub open spec fn best(nums: Seq<i32>, i: int, r: int) -> int
    recommends 0 <= r < 3, 0 <= i <= nums.len() as int
    decreases i
{
    if i <= 0 {
        0
    } else {
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        let prev = best(nums, i - 1, r);
        let prev_src = best(nums, i - 1, src);
        let take = prev_src + a;
        if (prev_src > 0 || src == 0) && take > prev {
            take
        } else {
            prev
        }
    }
}

proof fn lemma_best_nonneg(nums: Seq<i32>, i: int, r: int)
    requires
        0 <= r < 3,
        0 <= i <= nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
    ensures
        best(nums, i, r) >= 0,
    decreases i
{
    if i > 0 {
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        assert(0 <= src < 3);
        lemma_best_nonneg(nums, i - 1, r);
        lemma_best_nonneg(nums, i - 1, src);
    }
}

proof fn lemma_best_upper_bound(nums: Seq<i32>, i: int, r: int)
    requires
        0 <= r < 3,
        0 <= i <= nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
    ensures
        best(nums, i, r) <= 10000 * i,
    decreases i
{
    if i > 0 {
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        assert(0 <= src < 3);
        lemma_best_upper_bound(nums, i - 1, r);
        lemma_best_upper_bound(nums, i - 1, src);
        lemma_best_nonneg(nums, i - 1, r);
        lemma_best_nonneg(nums, i - 1, src);
    }
}


proof fn lemma_best_remainder(nums: Seq<i32>, i: int, r: int)
    requires
        0 <= r < 3,
        0 <= i <= nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
    ensures
        best(nums, i, r) % 3 == r || (best(nums, i, r) == 0 && r != 0),
        r == 0 ==> best(nums, i, r) % 3 == 0,
    decreases i
{
    if i > 0 {
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        assert(0 <= src < 3);
        lemma_best_nonneg(nums, i - 1, r);
        lemma_best_nonneg(nums, i - 1, src);
        lemma_best_remainder(nums, i - 1, r);
        lemma_best_remainder(nums, i - 1, src);
        let prev = best(nums, i - 1, r);
        let prev_src = best(nums, i - 1, src);
        let take = prev_src + a;
        if (prev_src > 0 || src == 0) && take > prev {
            
            assert(prev_src % 3 == src || (prev_src == 0 && src != 0));
            if src == 0 {
                assert(prev_src % 3 == 0);
                assert(ar == r) by (nonlinear_arith)
                    requires src == (r - ar + 3) % 3, src == 0, 0 <= r < 3, 0 <= ar < 3;
                assert((prev_src + a) % 3 == ar) by (nonlinear_arith)
                    requires prev_src % 3 == 0, ar == a % 3, a >= 1, prev_src >= 0;
            } else {
                assert(prev_src > 0);
                assert(prev_src % 3 == src);
                assert((prev_src + a) % 3 == (src + ar) % 3) by (nonlinear_arith)
                    requires prev_src % 3 == src, ar == a % 3, prev_src >= 1, a >= 1, 0 <= src < 3;
                assert((src + ar) % 3 == r) by (nonlinear_arith)
                    requires src == (r - ar + 3) % 3, 0 <= r < 3, 0 <= ar < 3, 0 <= src < 3;
            }
        }
    }
}


proof fn lemma_best_achievable(nums: Seq<i32>, i: int, r: int)
    requires
        0 <= r < 3,
        0 <= i <= nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
        best(nums, i, r) > 0 || r == 0,
    ensures
        exists |sel: Seq<bool>| sel.len() == nums.len()
            && subset_sum(nums, sel, i) == best(nums, i, r)
            && (forall |j: int| i <= j < nums.len() ==> (#[trigger] sel[j]) == false),
    decreases i
{
    if i <= 0 {
        
        let sel = Seq::new(nums.len(), |_j: int| false);
        assert(sel.len() == nums.len());
        assert forall |j: int| 0 <= j < nums.len() implies (#[trigger] sel[j]) == false by {
            assert(sel[j] == false);
        };
        assert(subset_sum(nums, sel, 0) == 0);
    } else {
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        assert(0 <= src < 3);
        lemma_best_nonneg(nums, i - 1, r);
        lemma_best_nonneg(nums, i - 1, src);
        let prev = best(nums, i - 1, r);
        let prev_src = best(nums, i - 1, src);
        let take = prev_src + a;
        if (prev_src > 0 || src == 0) && take > prev {
            
            lemma_best_achievable(nums, i - 1, src);
            let sel_base: Seq<bool> = choose |sel: Seq<bool>| sel.len() == nums.len()
                && subset_sum(nums, sel, i - 1) == best(nums, i - 1, src)
                && (forall |j: int| i - 1 <= j < nums.len() ==> (#[trigger] sel[j]) == false);
            let sel = sel_base.update(i - 1, true);
            assert(sel.len() == nums.len());
            assert(sel[i - 1] == true);
            
            
            assert forall |j: int| 0 <= j < i - 1 implies sel[j] == sel_base[j] by {};
            lemma_subset_sum_agree(nums, sel, sel_base, i - 1);
            assert(subset_sum(nums, sel, i - 1) == subset_sum(nums, sel_base, i - 1));
            assert(subset_sum(nums, sel, i) == nums[i - 1] as int + subset_sum(nums, sel, i - 1));
            assert(forall |j: int| i <= j < nums.len() ==> (#[trigger] sel[j]) == false);
        } else {
            
            if prev > 0 || r == 0 {
                lemma_best_achievable(nums, i - 1, r);
                let sel: Seq<bool> = choose |sel: Seq<bool>| sel.len() == nums.len()
                    && subset_sum(nums, sel, i - 1) == best(nums, i - 1, r)
                    && (forall |j: int| i - 1 <= j < nums.len() ==> (#[trigger] sel[j]) == false);
                assert(sel[i - 1] == false);
                assert(subset_sum(nums, sel, i) == subset_sum(nums, sel, i - 1));
                assert(forall |j: int| i <= j < nums.len() ==> (#[trigger] sel[j]) == false);
            }
        }
    }
}

proof fn lemma_subset_sum_agree(nums: Seq<i32>, a: Seq<bool>, b: Seq<bool>, hi: int)
    requires
        a.len() == b.len(),
        hi >= 0,
        forall |j: int| 0 <= j < hi ==> a[j] == b[j],
    ensures
        subset_sum(nums, a, hi) == subset_sum(nums, b, hi),
    decreases hi
{
    if hi > 0 {
        assert(a[hi - 1] == b[hi - 1]);
        lemma_subset_sum_agree(nums, a, b, hi - 1);
    }
}


proof fn lemma_best_optimal(nums: Seq<i32>, i: int, r: int, sel: Seq<bool>)
    requires
        0 <= r < 3,
        0 <= i <= nums.len(),
        sel.len() == nums.len(),
        forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 10000,
        subset_sum(nums, sel, i) % 3 == r,
        forall |j: int| i <= j < nums.len() ==> (#[trigger] sel[j]) == false,
    ensures
        subset_sum(nums, sel, i) <= best(nums, i, r),
    decreases i
{
    lemma_best_nonneg(nums, i, r);
    lemma_subset_sum_nonneg(nums, sel, i);
    if i <= 0 {
    } else if sel[i - 1] == false {
        
        assert(subset_sum(nums, sel, i) == subset_sum(nums, sel, i - 1));
        assert(forall |j: int| i - 1 <= j < nums.len() ==> (#[trigger] sel[j]) == false);
        lemma_best_nonneg(nums, i - 1, r);
        
        lemma_best_optimal(nums, i - 1, r, sel);
        
    } else {
        
        let a = nums[i - 1] as int;
        let ar = a % 3;
        let src = (r - ar + 3) % 3;
        assert(0 <= src < 3);
        lemma_best_nonneg(nums, i - 1, r);
        lemma_best_nonneg(nums, i - 1, src);

        let sub = subset_sum(nums, sel, i - 1);
        assert(subset_sum(nums, sel, i) == a + sub);
        lemma_subset_sum_nonneg(nums, sel, i - 1);

        
        assert(sub % 3 == src) by (nonlinear_arith)
            requires (a + sub) % 3 == r, ar == a % 3, src == (r - ar + 3) % 3,
                0 <= r < 3, 0 <= ar < 3, 0 <= src < 3, a >= 1, sub >= 0;

        
        let sel2 = sel.update(i - 1, false);
        assert(forall |j: int| i - 1 <= j < nums.len() ==> (#[trigger] sel2[j]) == false);
        assert forall |j: int| 0 <= j < i - 1 implies sel2[j] == sel[j] by {};
        lemma_subset_sum_agree(nums, sel2, sel, i - 1);
        assert(subset_sum(nums, sel2, i - 1) == sub);

        
        lemma_best_optimal(nums, i - 1, src, sel2);
        assert(sub <= best(nums, i - 1, src));

        
        let prev_src = best(nums, i - 1, src);
        let prev = best(nums, i - 1, r);
        let take = prev_src + a;
        assert(subset_sum(nums, sel, i) <= take);

        
        if prev_src > 0 || src == 0 {
            
            if take > prev {
                assert(best(nums, i, r) == take);
            } else {
                assert(best(nums, i, r) == prev);
                assert(best(nums, i, r) >= take);
            }
        } else {
            
            assert(sub <= prev_src);
            assert(sub == 0);
            assert(false) by (nonlinear_arith)
                requires sub == 0, sub % 3 == src, src >= 1, src < 3;
        }
    }
}

proof fn lemma_subset_sum_nonneg(nums: Seq<i32>, sel: Seq<bool>, hi: int)
    requires
        forall |j: int| 0 <= j < hi ==> #[trigger] nums[j] >= 1,
    ensures
        subset_sum(nums, sel, hi) >= 0,
    decreases hi
{
    if hi > 0 {
        lemma_subset_sum_nonneg(nums, sel, hi - 1);
    }
}

impl Solution {
    pub fn max_sum_div_three(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 40000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
        ensures
            result >= 0,
            result as int % 3 == 0,
            exists |sel: Seq<bool>| sel.len() == nums.len() as int
                && subset_sum(nums@, sel, nums.len() as int) == result as int,
            forall |sel: Seq<bool>| sel.len() == nums.len() as int
                && subset_sum(nums@, sel, nums.len() as int) % 3 == 0
                ==> subset_sum(nums@, sel, nums.len() as int) <= result as int,
    {
        let n = nums.len();
        let mut dp0: i32 = 0;
        let mut dp1: i32 = 0;
        let mut dp2: i32 = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 40000,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] nums@[j] <= 10000,
                dp0 as int == best(nums@, i as int, 0),
                dp1 as int == best(nums@, i as int, 1),
                dp2 as int == best(nums@, i as int, 2),
            decreases n - i,
        {
            proof {
                lemma_best_upper_bound(nums@, i as int, 0);
                lemma_best_upper_bound(nums@, i as int, 1);
                lemma_best_upper_bound(nums@, i as int, 2);
                lemma_best_nonneg(nums@, i as int, 0);
                lemma_best_nonneg(nums@, i as int, 1);
                lemma_best_nonneg(nums@, i as int, 2);
                assert(dp0 as int <= 10000 * (i as int));
                assert(dp1 as int <= 10000 * (i as int));
                assert(dp2 as int <= 10000 * (i as int));
                assert(10000 * (i as int) <= 10000 * 40000);
            }

            let a = nums[i];
            let old0 = dp0;
            let old1 = dp1;
            let old2 = dp2;
            let r = a % 3;

            if r == 0 {
                dp0 = old0 + a;
                dp1 = if old1 > 0 { old1 + a } else { old1 };
                dp2 = if old2 > 0 { old2 + a } else { old2 };
            } else if r == 1 {
                let new_dp0 = if old2 > 0 && old2 + a > old0 { old2 + a } else { old0 };
                let new_dp1 = if old0 + a > old1 { old0 + a } else { old1 };
                let new_dp2 = if old1 > 0 && old1 + a > old2 { old1 + a } else { old2 };
                dp0 = new_dp0;
                dp1 = new_dp1;
                dp2 = new_dp2;
            } else {
                let new_dp0 = if old1 > 0 && old1 + a > old0 { old1 + a } else { old0 };
                let new_dp1 = if old2 > 0 && old2 + a > old1 { old2 + a } else { old1 };
                let new_dp2 = if old0 + a > old2 { old0 + a } else { old2 };
                dp0 = new_dp0;
                dp1 = new_dp1;
                dp2 = new_dp2;
            }

            i += 1;
        }

        proof {
            let n_int = n as int;
            
            lemma_best_nonneg(nums@, n_int, 0);

            
            lemma_best_remainder(nums@, n_int, 0);

            
            lemma_best_achievable(nums@, n_int, 0);
            let sel_witness: Seq<bool> = choose |sel: Seq<bool>| sel.len() == nums@.len()
                && subset_sum(nums@, sel, n_int) == best(nums@, n_int, 0)
                && (forall |j: int| n_int <= j < nums@.len() ==> (#[trigger] sel[j]) == false);

            
            assert forall |sel: Seq<bool>| sel.len() == n_int
                && subset_sum(nums@, sel, n_int) % 3 == 0
                implies subset_sum(nums@, sel, n_int) <= dp0 as int by {
                lemma_best_optimal(nums@, n_int, 0, sel);
            };
        }

        dp0
    }
}

}
