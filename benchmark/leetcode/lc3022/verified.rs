use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fits(v: i32, target: i32) -> bool {
        (v | target) == target
    }

    pub open spec fn min_ops_from(nums: Seq<i32>, target: i32, i: int, cur: i32) -> int
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            0
        } else {
            let cur2 = cur & nums[i];
            if Self::fits(cur2, target) {
                let a = Self::min_ops_from(nums, target, i + 1, 1_073_741_823i32);
                let b = 1 + Self::min_ops_from(nums, target, i + 1, cur2);
                if a < b { a } else { b }
            } else {
                1 + Self::min_ops_from(nums, target, i + 1, cur2)
            }
        }
    }

    pub open spec fn greedy_from(nums: Seq<i32>, target: i32, i: int, cur: i32) -> int
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            0
        } else {
            let cur2 = cur & nums[i];
            if Self::fits(cur2, target) {
                Self::greedy_from(nums, target, i + 1, 1_073_741_823i32)
            } else {
                1 + Self::greedy_from(nums, target, i + 1, cur2)
            }
        }
    }

    pub open spec fn achievable(nums: Seq<i32>, k: int, target: i32) -> bool {
        Self::min_ops_from(nums, target, 0, 1_073_741_823i32) <= k
    }

    pub open spec fn pow2(e: int) -> int
        decreases e when e >= 0
    {
        if e <= 0 { 1 } else { 2 * Self::pow2(e - 1) }
    }

    proof fn lemma_pow2_base()
        ensures
            Self::pow2(29) == 536_870_912,
    {
        reveal_with_fuel(Solution::pow2, 30);
        assert(Self::pow2(29) == 536_870_912);
    }

    proof fn lemma_pow2_ge(e: int)
        requires
            0 <= e,
        ensures
            Self::pow2(e) >= 1,
            e >= 1 ==> Self::pow2(e) >= 2,
        decreases e,
    {
        if e <= 0 {
        } else {
            Self::lemma_pow2_ge(e - 1);
        }
    }

    proof fn lemma_pow2_step(e: int)
        requires
            e >= 1,
        ensures
            Self::pow2(e) == 2 * Self::pow2(e - 1),
    {
    }

    proof fn lemma_subset_trans(x: i32, y: i32, z: i32)
        requires
            (x | y) == y,
            (y | z) == z,
        ensures
            (x | z) == z,
    {
        assert((x | z) == z) by (bit_vector)
            requires
                (x | y) == y,
                (y | z) == z;
    }

    proof fn lemma_and_mono(a: i32, b: i32, x: i32)
        requires
            (a | b) == b,
        ensures
            ((a & x) | (b & x)) == (b & x),
    {
        assert(((a & x) | (b & x)) == (b & x)) by (bit_vector)
            requires
                (a | b) == b;
    }

    proof fn lemma_all_is_top(v: i32)
        requires
            0 <= v < 1_073_741_824,
        ensures
            (v | 1_073_741_823i32) == 1_073_741_823i32,
    {
        assert((v | 1_073_741_823i32) == 1_073_741_823i32) by (bit_vector)
            requires
                0 <= v < 1_073_741_824;
    }

    proof fn lemma_cur_mono(nums: Seq<i32>, target: i32, i: int, cur_a: i32, cur_b: i32)
        requires
            0 <= i <= nums.len(),
            (cur_a | cur_b) == cur_b,
        ensures
            Self::min_ops_from(nums, target, i, cur_a) <= Self::min_ops_from(nums, target, i, cur_b),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let cur_a2 = cur_a & nums[i];
            let cur_b2 = cur_b & nums[i];
            Self::lemma_and_mono(cur_a, cur_b, nums[i]);
            if Self::fits(cur_b2, target) {
                Self::lemma_subset_trans(cur_a2, cur_b2, target);
                Self::lemma_cur_mono(nums, target, i + 1, cur_a2, cur_b2);
            } else {
                if Self::fits(cur_a2, target) {
                    Self::lemma_cur_mono(nums, target, i + 1, cur_a2, cur_b2);
                } else {
                    Self::lemma_cur_mono(nums, target, i + 1, cur_a2, cur_b2);
                }
            }
        }
    }

    proof fn lemma_reset_bound(nums: Seq<i32>, target: i32, i: int, cur: i32)
        requires
            0 <= i <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] < 1_073_741_824,
        ensures
            Self::min_ops_from(nums, target, i, 1_073_741_823i32)
                <= 1 + Self::min_ops_from(nums, target, i, cur),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let ni = nums[i];
            let a2 = 1_073_741_823i32 & ni;
            let c2 = cur & ni;
            assert(a2 == ni) by (bit_vector)
                requires
                    0 <= ni < 1_073_741_824,
                    a2 == (1_073_741_823i32 & ni);
            Self::lemma_reset_bound(nums, target, i + 1, c2);
            if Self::fits(a2, target) {
            } else {
                Self::lemma_all_is_top(ni);
                Self::lemma_cur_mono(nums, target, i + 1, a2, 1_073_741_823i32);
            }
        }
    }

    proof fn lemma_greedy_eq_minops(nums: Seq<i32>, target: i32, i: int, cur: i32)
        requires
            0 <= i <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] < 1_073_741_824,
        ensures
            Self::greedy_from(nums, target, i, cur) == Self::min_ops_from(nums, target, i, cur),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let cur2 = cur & nums[i];
            Self::lemma_greedy_eq_minops(nums, target, i + 1, 1_073_741_823i32);
            Self::lemma_greedy_eq_minops(nums, target, i + 1, cur2);
            if Self::fits(cur2, target) {
                Self::lemma_reset_bound(nums, target, i + 1, cur2);
            }
        }
    }

    proof fn lemma_target_mono(nums: Seq<i32>, i: int, cur: i32, t1: i32, t2: i32)
        requires
            0 <= i <= nums.len(),
            (t1 | t2) == t2,
        ensures
            Self::min_ops_from(nums, t1, i, cur) >= Self::min_ops_from(nums, t2, i, cur),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let cur2 = cur & nums[i];
            Self::lemma_target_mono(nums, i + 1, 1_073_741_823i32, t1, t2);
            Self::lemma_target_mono(nums, i + 1, cur2, t1, t2);
            if Self::fits(cur2, t1) {
                Self::lemma_subset_trans(cur2, t1, t2);
            }
        }
    }

    proof fn lemma_achievable_mono(nums: Seq<i32>, k: int, t1: i32, t2: i32)
        requires
            (t1 | t2) == t2,
            Self::achievable(nums, k, t1),
        ensures
            Self::achievable(nums, k, t2),
    {
        Self::lemma_target_mono(nums, 0, 1_073_741_823i32, t1, t2);
    }

    proof fn lemma_and_in_range(a: i32, b: i32)
        requires
            0 <= a < 1_073_741_824,
            0 <= b < 1_073_741_824,
        ensures
            0 <= (a & b) < 1_073_741_824,
    {
        assert(0 <= (a & b) < 1_073_741_824) by (bit_vector)
            requires
                0 <= a < 1_073_741_824,
                0 <= b < 1_073_741_824;
    }

    proof fn lemma_or_in_range(a: i32, b: i32)
        requires
            0 <= a < 1_073_741_824,
            0 <= b < 1_073_741_824,
        ensures
            0 <= (a | b) < 1_073_741_824,
    {
        assert(0 <= (a | b) < 1_073_741_824) by (bit_vector)
            requires
                0 <= a < 1_073_741_824,
                0 <= b < 1_073_741_824;
    }

    proof fn lemma_min_ops_nonneg(nums: Seq<i32>, target: i32, i: int, cur: i32)
        requires
            0 <= i <= nums.len(),
        ensures
            Self::min_ops_from(nums, target, i, cur) >= 0,
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let cur2 = cur & nums[i];
            Self::lemma_min_ops_nonneg(nums, target, i + 1, 1_073_741_823i32);
            Self::lemma_min_ops_nonneg(nums, target, i + 1, cur2);
        }
    }

    proof fn lemma_min_ops_all_target_zero(nums: Seq<i32>, i: int, cur: i32)
        requires
            0 <= i <= nums.len(),
            0 <= cur < 1_073_741_824,
            forall |t: int| 0 <= t < nums.len() ==> 0 <= #[trigger] nums[t] < 1_073_741_824,
        ensures
            Self::min_ops_from(nums, 1_073_741_823i32, i, cur) == 0,
        decreases nums.len() - i,
    {
        if i >= nums.len() {
        } else {
            let ni = nums[i];
            let cur2 = cur & ni;
            Self::lemma_and_in_range(cur, ni);
            Self::lemma_all_is_top(cur2);
            Self::lemma_min_ops_all_target_zero(nums, i + 1, 1_073_741_823i32);
            Self::lemma_min_ops_nonneg(nums, 1_073_741_823i32, i + 1, cur2);
        }
    }

    proof fn lemma_pow2_halve_preserved(b: i32)
        requires
            b > 0i32,
            b <= 1_000_000_000i32,
            (b & ((b - 1i32) as i32)) == 0i32,
        ensures
            ((b / 2i32) as i32) == 0i32
                || (((((b / 2i32) as i32) & (((b / 2i32) as i32 - 1i32) as i32)) as i32) == 0i32),
    {
        assert(
            ((b / 2i32) as i32) == 0i32
                || (((((b / 2i32) as i32) & (((b / 2i32) as i32 - 1i32) as i32)) as i32) == 0i32)
        ) by (bit_vector)
            requires
                b > 0i32,
                b <= 1_000_000_000i32,
                (b & ((b - 1i32) as i32)) == 0i32;
    }

    proof fn lemma_half_identity(b: i32)
        requires
            b >= 2i32,
            b <= 1_000_000_000i32,
            (b & ((b - 1i32) as i32)) == 0i32,
        ensures
            (((((b / 2i32) as i32 - 1i32) as i32) | ((b / 2i32) as i32)) as i32)
                == ((b - 1i32) as i32),
    {
        assert(
            (((((b / 2i32) as i32 - 1i32) as i32) | ((b / 2i32) as i32)) as i32)
                == ((b - 1i32) as i32)
        ) by (bit_vector)
            requires
                b >= 2i32,
                b <= 1_000_000_000i32,
                (b & ((b - 1i32) as i32)) == 0i32;
    }

    proof fn lemma_struct_maintain(ans: i32, bit_val: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32,
        ensures
            (ans & ((bit_val - 1i32) as i32)) == 0i32,
            (((ans | bit_val) as i32) & ((bit_val - 1i32) as i32)) == 0i32,
    {
        assert((ans & ((bit_val - 1i32) as i32)) == 0i32) by (bit_vector)
            requires
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32;
        assert(
            (((ans | bit_val) as i32) & ((bit_val - 1i32) as i32)) == 0i32
        ) by (bit_vector)
            requires
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32;
    }

    proof fn lemma_or_assoc(a: i32, b: i32, c: i32)
        ensures
            ((a | b) as i32 | c) as i32 == (a | (b | c) as i32) as i32,
    {
        assert(((a | b) as i32 | c) as i32 == (a | (b | c) as i32) as i32) by (bit_vector);
    }

    proof fn lemma_div_mono_strict(v: int, p: int, b: int, h: int)
        requires
            b == 2 * h,
            h >= 1,
            v >= (p + 1) * b,
        ensures
            v / h >= 2 * (p + 1),
    {
        assert(v / h >= 2 * (p + 1)) by (nonlinear_arith)
            requires
                b == 2 * h,
                h >= 1,
                v >= (p + 1) * b;
    }

    proof fn lemma_div_boundary(v: int, p: int, b: int, h: int)
        requires
            b == 2 * h,
            h >= 1,
            v / b == p,
        ensures
            v / h == 2 * p || v / h == 2 * p + 1,
    {
        assert(v / h == 2 * p || v / h == 2 * p + 1) by (nonlinear_arith)
            requires
                b == 2 * h,
                h >= 1,
                v / b == p;
    }

    proof fn lemma_exact_multiple_div(p: int, b: int, h: int)
        requires
            b == 2 * h,
            h >= 1,
        ensures
            (p * b) / h == 2 * p,
    {
        assert((p * b) / h == 2 * p) by (nonlinear_arith)
            requires
                b == 2 * h,
                h >= 1;
    }

    proof fn lemma_div_gt_implies_ge_mult(v: int, p: int, b: int)
        requires
            b >= 1,
            v / b > p,
        ensures
            v >= (p + 1) * b,
    {
        assert(v >= (p + 1) * b) by (nonlinear_arith)
            requires
                b >= 1,
                v / b > p;
    }

    proof fn lemma_clear_low_bits_exact_multiple(ans: i32, b: i32)
        requires
            b >= 2i32,
            b <= 536_870_912i32,
            (b & ((b - 1i32) as i32)) == 0i32,
            ans >= 0i32,
            ans < 1_073_741_824i32,
            (ans & ((b - 1i32) as i32)) == 0i32,
        ensures
            (ans as int) == ((ans as int) / (b as int)) * (b as int),
    {
        assert((ans as int) == ((ans as int) / (b as int)) * (b as int)) by (bit_vector)
            requires
                b >= 2i32,
                b <= 536_870_912i32,
                (b & ((b - 1i32) as i32)) == 0i32,
                ans >= 0i32,
                ans < 1_073_741_824i32,
                (ans & ((b - 1i32) as i32)) == 0i32;
    }

    proof fn lemma_half_exact(bit_val: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
        ensures
            bit_val as int == 2 * ((bit_val / 2i32) as int),
    {
        assert(bit_val as int == 2 * ((bit_val / 2i32) as int)) by (bit_vector)
            requires
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32;
    }

    proof fn lemma_feas_identity_no_set(ans: i32, bit_val: i32, target: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            target == ((ans | ((bit_val - 1i32) as i32)) as i32),
        ensures
            (((ans | (((bit_val / 2i32) as i32 - 1i32) as i32)) as i32) | ((bit_val / 2i32) as i32)) as i32
                == target,
    {
        assert(
            (((ans | (((bit_val / 2i32) as i32 - 1i32) as i32)) as i32) | ((bit_val / 2i32) as i32)) as i32
                == target
        ) by (bit_vector)
            requires
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                target == ((ans | ((bit_val - 1i32) as i32)) as i32);
    }

    proof fn lemma_feas_identity_set(ans: i32, bit_val: i32, ans_new: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            ans_new == ((ans | bit_val) as i32),
        ensures
            (((ans_new | (((bit_val / 2i32) as i32 - 1i32) as i32)) as i32) | ((bit_val / 2i32) as i32)) as i32
                == (((ans | ((bit_val - 1i32) as i32)) as i32) | bit_val) as i32,
    {
        assert(
            (((ans_new | (((bit_val / 2i32) as i32 - 1i32) as i32)) as i32) | ((bit_val / 2i32) as i32)) as i32
                == (((ans | ((bit_val - 1i32) as i32)) as i32) | bit_val) as i32
        ) by (bit_vector)
            requires
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                ans_new == ((ans | bit_val) as i32);
    }

    proof fn lemma_target_same_prefix(ans: i32, bit_val: i32, target: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            ans >= 0i32,
            ans < 1_073_741_824i32,
            (ans & ((bit_val - 1i32) as i32)) == 0i32,
            target == ((ans | ((bit_val - 1i32) as i32)) as i32),
        ensures
            (target as int / bit_val as int) == (ans as int / bit_val as int),
            (target & ((bit_val - 1i32) as i32)) == ((bit_val - 1i32) as i32),
    {
        assert(
            (target as int / bit_val as int) == (ans as int / bit_val as int)
        ) by (bit_vector)
            requires
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                ans >= 0i32,
                ans < 1_073_741_824i32,
                (ans & ((bit_val - 1i32) as i32)) == 0i32,
                target == ((ans | ((bit_val - 1i32) as i32)) as i32);
        assert(
            (target & ((bit_val - 1i32) as i32)) == ((bit_val - 1i32) as i32)
        ) by (bit_vector)
            requires
                target == ((ans | ((bit_val - 1i32) as i32)) as i32);
    }

    proof fn lemma_v_subset_target(v: i32, target: i32, b: i32)
        requires
            b >= 2i32,
            b <= 536_870_912i32,
            (b & ((b - 1i32) as i32)) == 0i32,
            v >= 0i32,
            v < 1_073_741_824i32,
            target >= 0i32,
            target < 1_073_741_824i32,
            (v as int / b as int) == (target as int / b as int),
            (target & ((b - 1i32) as i32)) == ((b - 1i32) as i32),
        ensures
            (v | target) == target,
    {
        assert((v | target) == target) by (bit_vector)
            requires
                b >= 2i32,
                b <= 536_870_912i32,
                (b & ((b - 1i32) as i32)) == 0i32,
                v >= 0i32,
                v < 1_073_741_824i32,
                target >= 0i32,
                target < 1_073_741_824i32,
                (v as int / b as int) == (target as int / b as int),
                (target & ((b - 1i32) as i32)) == ((b - 1i32) as i32);
    }

    proof fn lemma_opt_step_no_set(nums: Seq<i32>, k: int, ans: i32, bit_val: i32, target: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            ans >= 0i32,
            ans < 1_073_741_824i32,
            (ans & ((bit_val - 1i32) as i32)) == 0i32,
            target == ((ans | ((bit_val - 1i32) as i32)) as i32),
            Self::achievable(nums, k, target),
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> (v as int / bit_val as int) >= (ans as int / bit_val as int),
        ensures
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> (v as int / (bit_val / 2i32) as int) >= (ans as int / (bit_val / 2i32) as int),
    {
        let h: i32 = (bit_val / 2i32) as i32;
        Self::lemma_half_exact(bit_val);
        let p: int = ans as int / bit_val as int;
        Self::lemma_target_same_prefix(ans, bit_val, target);
        Self::lemma_exact_multiple_div(p, bit_val as int, h as int);
        Self::lemma_clear_low_bits_exact_multiple(ans, bit_val);
        assert forall |v: i32|
            (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
            implies (v as int / h as int) >= (ans as int / h as int) by {
            if (v as int / bit_val as int) > p {
                Self::lemma_div_gt_implies_ge_mult(v as int, p, bit_val as int);
                Self::lemma_div_mono_strict(v as int, p, bit_val as int, h as int);
            } else {
                Self::lemma_or_in_range(ans, (bit_val - 1i32) as i32);
                Self::lemma_v_subset_target(v, target, bit_val);
                Self::lemma_achievable_mono(nums, k, v, target);
                Self::lemma_div_boundary(v as int, p, bit_val as int, h as int);
            }
        }
    }

    proof fn lemma_opt_step_set(nums: Seq<i32>, k: int, ans: i32, bit_val: i32, target: i32, ans_new: i32)
        requires
            bit_val >= 2i32,
            bit_val <= 536_870_912i32,
            (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
            ans >= 0i32,
            ans < 1_073_741_824i32,
            (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32,
            target == ((ans | ((bit_val - 1i32) as i32)) as i32),
            ans_new == ((ans | bit_val) as i32),
            !Self::achievable(nums, k, target),
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> (v as int / bit_val as int) >= (ans as int / bit_val as int),
        ensures
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> (v as int / (bit_val / 2i32) as int) >= (ans_new as int / (bit_val / 2i32) as int),
    {
        let h: i32 = (bit_val / 2i32) as i32;
        Self::lemma_half_exact(bit_val);
        let p: int = ans as int / bit_val as int;
        Self::lemma_struct_maintain(ans, bit_val);
        Self::lemma_target_same_prefix(ans, bit_val, target);
        Self::lemma_clear_low_bits_exact_multiple(ans, bit_val);
        assert(ans_new as int == ans as int + bit_val as int) by (bit_vector)
            requires
                ans_new == ((ans | bit_val) as i32),
                bit_val >= 2i32,
                bit_val <= 536_870_912i32,
                (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32;
        assert(ans_new as int == (p + 1) * bit_val as int) by (nonlinear_arith)
            requires
                ans_new as int == ans as int + bit_val as int,
                ans as int == p * bit_val as int;
        Self::lemma_exact_multiple_div(p + 1, bit_val as int, h as int);
        assert forall |v: i32|
            (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
            implies (v as int / h as int) >= (ans_new as int / h as int) by {
            if (v as int / bit_val as int) > p {
                Self::lemma_div_gt_implies_ge_mult(v as int, p, bit_val as int);
                Self::lemma_div_mono_strict(v as int, p, bit_val as int, h as int);
            } else {
                Self::lemma_or_in_range(ans, (bit_val - 1i32) as i32);
                Self::lemma_v_subset_target(v, target, bit_val);
                Self::lemma_achievable_mono(nums, k, v, target);
                assert(false);
            }
        }
    }

    proof fn lemma_opt_final_set(nums: Seq<i32>, k: int, ans: i32, ans_new: i32)
        requires
            ans_new == ans + 1i32,
            ans >= 0i32,
            ans < 1_073_741_824i32,
            !Self::achievable(nums, k, ans),
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> v as int >= ans as int,
        ensures
            forall |v: i32| (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
                ==> v as int >= ans_new as int,
    {
        assert forall |v: i32|
            (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums, k, v))
            implies v as int >= ans_new as int by {
            if v == ans {
                assert((v | ans) == ans);
                Self::lemma_achievable_mono(nums, k, v, ans);
                assert(false);
            }
        }
    }

    pub fn min_or_after_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            0 <= k < nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
        ensures
            Self::achievable(nums@, k as int, result),
            forall |v: i32| 0 <= v < 1_073_741_824i32 && Self::achievable(nums@, k as int, v)
                ==> result as int <= v as int,
    {
        let all: i32 = 1_073_741_823;
        let n = nums.len();
        let mut ans: i32 = 0;
        let mut bit: i32 = 29;
        let mut bit_val: i32 = 536_870_912;

        proof {
            Self::lemma_min_ops_all_target_zero(nums@, 0, 1_073_741_823i32);
            assert(bit_val == 0i32 || (bit_val & ((bit_val - 1i32) as i32)) == 0i32) by (bit_vector)
                requires bit_val == 536_870_912i32;
            assert((ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32) by (bit_vector)
                requires ans == 0i32;
            assert((((ans | ((bit_val - 1i32) as i32)) as i32) | bit_val) as i32
                == 1_073_741_823i32) by (bit_vector)
                requires ans == 0i32, bit_val == 536_870_912i32;
            Self::lemma_pow2_base();
        }

        while bit >= 0
            invariant
                n == nums.len(),
                1 <= n <= 100000,
                0 <= k < n,
                all == 1_073_741_823i32,
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
                -1 <= bit <= 29,
                0 <= bit_val <= 536_870_912,
                0 <= ans < 1_073_741_824,
                bit >= 0 ==> bit_val as int == Self::pow2(bit as int),
                bit == -1 ==> bit_val == 0,
                bit_val == 0 || (bit_val & ((bit_val - 1i32) as i32)) == 0i32,
                bit_val > 0 ==> (ans & ((2i32 * bit_val - 1i32) as i32)) == 0i32,
                bit_val > 0 ==> Self::achievable(
                    nums@, k as int,
                    (((ans | ((bit_val - 1i32) as i32)) as i32) | bit_val) as i32,
                ),
                bit_val == 0 ==> Self::achievable(nums@, k as int, ans),
                bit_val > 0 ==> forall |v: i32|
                    (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums@, k as int, v))
                    ==> (ans as int / bit_val as int) <= (v as int / bit_val as int),
                bit_val == 0 ==> forall |v: i32|
                    (0 <= v < 1_073_741_824i32 && #[trigger] Self::achievable(nums@, k as int, v))
                    ==> ans as int <= v as int,
            decreases bit + 1,
        {
            let target = ans | (bit_val - 1);
            let mut cnt: i32 = 0;
            let mut cur: i32 = all;
            let mut idx: usize = 0;

            proof {
                assert(cur == 1_073_741_823i32);
            }
            proof {
                assert(0 <= cur < 1_073_741_824i32);
            }
            proof {
                assert(Self::greedy_from(nums@, target, 0, 1_073_741_823i32)
                    == cnt as int + Self::greedy_from(nums@, target, idx as int, cur));
            }

            while idx < n
                invariant
                    n == nums.len(),
                    n <= 100000,
                    0 <= idx <= n,
                    0 <= cnt <= idx,
                    0 <= cur < 1_073_741_824,
                    all == 1_073_741_823i32,
                    ans >= 0i32,
                    ans < 1_073_741_824i32,
                    bit_val >= 0i32,
                    bit_val <= 536_870_912i32,
                    target == ans | ((bit_val - 1i32) as i32),
                    forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 1_073_741_824,
                    Self::greedy_from(nums@, target, 0, 1_073_741_823i32)
                        == cnt as int + Self::greedy_from(nums@, target, idx as int, cur),
                decreases n - idx,
            {
                let cur_before: i32 = cur;
                cur = cur & nums[idx];
                proof {
                    assert(cur == cur_before & nums@[idx as int]);
                }
                if (cur | target) == target {
                    proof {
                        assert(Self::fits(cur, target));
                        assert(Self::greedy_from(nums@, target, idx as int, cur_before)
                            == Self::greedy_from(nums@, target, idx as int + 1, 1_073_741_823i32));
                    }
                    cur = all;
                } else {
                    proof {
                        assert(!Self::fits(cur, target));
                        assert(Self::greedy_from(nums@, target, idx as int, cur_before)
                            == 1 + Self::greedy_from(nums@, target, idx as int + 1, cur));
                        Self::lemma_and_in_range(cur_before, nums@[idx as int]);
                    }
                    cnt = cnt + 1;
                }
                idx = idx + 1;
            }

            proof {
                Self::lemma_greedy_eq_minops(nums@, target, 0, 1_073_741_823i32);
                Self::lemma_pow2_ge(bit as int);
            }

            let ans_before: i32 = ans;
            if cnt > k {
                proof {
                    Self::lemma_or_in_range(ans, bit_val);
                }
                ans = ans | bit_val;
                if bit_val == 1 {
                    proof {
                        assert(target == ans_before) by (bit_vector)
                            requires
                                target == ans_before | ((bit_val - 1i32) as i32),
                                bit_val == 1i32;
                        assert(ans == ((ans_before + 1i32) as i32)) by (bit_vector)
                            requires
                                ans == ((ans_before | bit_val) as i32),
                                bit_val == 1i32,
                                (ans_before & ((2i32 * bit_val - 1i32) as i32)) == 0i32;
                        Self::lemma_opt_final_set(nums@, k as int, ans_before, ans);
                    }
                } else {
                    proof {
                        Self::lemma_struct_maintain(ans_before, bit_val);
                        Self::lemma_half_exact(bit_val);
                        Self::lemma_half_identity(bit_val);
                        Self::lemma_or_assoc(ans_before, bit_val, (bit_val - 1i32) as i32);
                        Self::lemma_opt_step_set(nums@, k as int, ans_before, bit_val, target, ans);
                        Self::lemma_feas_identity_set(ans_before, bit_val, ans);
                    }
                }
            } else {
                if bit_val >= 2 {
                    proof {
                        Self::lemma_struct_maintain(ans, bit_val);
                        Self::lemma_half_exact(bit_val);
                        Self::lemma_half_identity(bit_val);
                        Self::lemma_or_assoc(ans, ((bit_val / 2i32 - 1i32) as i32), (bit_val / 2i32) as i32);
                        Self::lemma_opt_step_no_set(nums@, k as int, ans, bit_val, target);
                        Self::lemma_feas_identity_no_set(ans, bit_val, target);
                    }
                } else if bit_val == 1 {
                    proof {
                        assert(target == ans) by (bit_vector)
                            requires
                                target == ans | ((bit_val - 1i32) as i32),
                                bit_val == 1i32;
                    }
                }
            }

            proof {
                if bit_val > 0 {
                    Self::lemma_pow2_halve_preserved(bit_val);
                }
                if bit >= 1 {
                    Self::lemma_pow2_step(bit as int);
                }
            }

            bit = bit - 1;
            if bit_val > 0 {
                bit_val = bit_val / 2;
            }
        }

        ans
    }
}

}
