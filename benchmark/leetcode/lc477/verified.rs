use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn hamming_distance_spec_helper(x: nat, acc: nat) -> nat
        decreases x,
    {
        if x == 0 {
            acc
        } else {
            let ones = x % 2;
            let new_acc = acc + ones;
            Solution::hamming_distance_spec_helper(x / 2, new_acc)
        }
    }

    pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
        Solution::hamming_distance_spec_helper(xor_result, 0)
    }

    proof fn hamming_distance_properties(x: nat, a: nat)
        ensures
            Solution::hamming_distance_spec_helper(x, a) == Solution::hamming_distance_spec_helper(
                x / 2, a + (x % 2)),
            Solution::hamming_distance_spec_helper(x, a) == a + Solution::hamming_distance_spec_helper(x, 0),
        decreases x,
    {
        if x == 0 {
        } else {
            Solution::hamming_distance_properties(x / 2, a + (x % 2));
            Solution::hamming_distance_properties(x / 2, x % 2);
        }
    }

    pub open spec fn pow2(e: nat) -> nat
        decreases e
    {
        if e == 0 { 1 } else { 2 * Solution::pow2((e - 1) as nat) }
    }

    proof fn lemma_pow2_pos(e: nat)
        ensures
            Solution::pow2(e) >= 1,
        decreases e,
    {
        if e == 0 {
        } else {
            Solution::lemma_pow2_pos((e - 1) as nat);
        }
    }

    pub open spec fn diff_bit_sum(a: nat, b: nat, num_bits: nat) -> nat
        decreases num_bits
    {
        if num_bits == 0 { 0 }
        else {
            let d: nat = if (a % 2) != (b % 2) { 1nat } else { 0nat };
            d + Solution::diff_bit_sum(a / 2, b / 2, (num_bits - 1) as nat)
        }
    }

    proof fn lemma_xor_nonneg_bound(ai: i32, bi: i32)
        requires
            0 <= ai <= i32::MAX,
            0 <= bi <= i32::MAX,
        ensures
            0 <= (ai ^ bi) <= i32::MAX,
    {
        assert(0 <= (ai ^ bi) <= i32::MAX) by (bit_vector)
            requires
                0 <= ai <= i32::MAX,
                0 <= bi <= i32::MAX;
    }

    proof fn lemma_hamming_eq_diff_bit_sum(a: nat, b: nat, xor_val: nat, num_bits: nat)
        requires
            xor_val == ((a as i32) ^ (b as i32)) as nat,
            a < Solution::pow2(num_bits),
            b < Solution::pow2(num_bits),
            a <= i32::MAX as nat,
            b <= i32::MAX as nat,
        ensures
            Solution::hamming_distance_spec_helper(xor_val, 0) == Solution::diff_bit_sum(a, b, num_bits),
        decreases num_bits
    {
        let ai: i32 = a as i32;
        let bi: i32 = b as i32;
        Solution::lemma_xor_nonneg_bound(ai, bi);
        let xi: i32 = ai ^ bi;
        assert(xor_val == xi as nat);
        assert(xi == xor_val as i32);

        if num_bits == 0 {
            assert(Solution::pow2(0) == 1);
            assert(a == 0 && b == 0);
            assert(ai == 0i32 && bi == 0i32);
            assert(xi == 0i32) by (bit_vector)
                requires
                    xi == ai ^ bi,
                    ai == 0i32,
                    bi == 0i32;
            assert(xor_val == 0);
        } else {
            let a2 = a / 2;
            let b2 = b / 2;
            let xor2 = xor_val / 2;
            assert(Solution::pow2(num_bits) == 2 * Solution::pow2((num_bits - 1) as nat));
            Solution::lemma_pow2_pos((num_bits - 1) as nat);
            assert(a2 < Solution::pow2((num_bits - 1) as nat)) by (nonlinear_arith)
                requires
                    a < 2 * Solution::pow2((num_bits - 1) as nat),
                    a2 == a / 2;
            assert(b2 < Solution::pow2((num_bits - 1) as nat)) by (nonlinear_arith)
                requires
                    b < 2 * Solution::pow2((num_bits - 1) as nat),
                    b2 == b / 2;

            let a2i: i32 = a2 as i32;
            let b2i: i32 = b2 as i32;
            assert(a2i == ai / 2) by (nonlinear_arith)
                requires
                    a2i == a2 as i32,
                    ai == a as i32,
                    a2 == a / 2,
                    0 <= a as int <= i32::MAX as int;
            assert(b2i == bi / 2) by (nonlinear_arith)
                requires
                    b2i == b2 as i32,
                    bi == b as i32,
                    b2 == b / 2,
                    0 <= b as int <= i32::MAX as int;
            let x2i: i32 = (xi / 2) as i32;
            assert(x2i == (a2i ^ b2i)) by (bit_vector)
                requires
                    xi == ai ^ bi,
                    0 <= ai,
                    0 <= bi,
                    a2i == ai / 2,
                    b2i == bi / 2,
                    x2i == xi / 2;
            Solution::lemma_xor_nonneg_bound(a2i, b2i);
            assert(xor2 == x2i as nat) by (nonlinear_arith)
                requires
                    xor2 == xor_val / 2,
                    xor_val == xi as nat,
                    x2i == xi / 2,
                    0 <= xi as int <= i32::MAX as int;
            assert(x2i == a2i ^ b2i);
            assert(xor2 == ((a2 as i32) ^ (b2 as i32)) as nat);

            assert((xi % 2 == 1i32) == ((ai % 2 == 1i32) != (bi % 2 == 1i32))) by (bit_vector)
                requires
                    xi == ai ^ bi,
                    0 <= ai,
                    0 <= bi;
            assert(xor_val % 2 == (xi % 2) as nat) by (nonlinear_arith)
                requires
                    xor_val == xi as nat,
                    0 <= xi;
            assert(a % 2 == (ai % 2) as nat) by (nonlinear_arith)
                requires
                    a == ai as nat,
                    0 <= ai;
            assert(b % 2 == (bi % 2) as nat) by (nonlinear_arith)
                requires
                    b == bi as nat,
                    0 <= bi;
            assert((xor_val % 2) == (if (a % 2) != (b % 2) { 1nat } else { 0nat }));
            Solution::hamming_distance_properties(xor_val, 0);
            Solution::hamming_distance_properties(xor2, xor_val % 2);
            Solution::lemma_hamming_eq_diff_bit_sum(a2, b2, xor2, (num_bits - 1) as nat);
        }
    }

    pub open spec fn total_hamming_distance_spec(nums: Seq<i32>, i: nat, j: nat, acc: nat) -> nat
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
            acc
        } else if j >= nums.len() {
            Solution::total_hamming_distance_spec(nums, i + 1, i + 2, acc)
        } else {
            let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
            let dist = Solution::hamming_distance_spec(xor_val);
            Solution::total_hamming_distance_spec(nums, i, j + 1, acc + dist)
        }
    }

    pub open spec fn total_diff_bit_sum(nums: Seq<i32>, i: nat, j: nat, num_bits: nat) -> nat
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
            0
        } else if j >= nums.len() {
            Solution::total_diff_bit_sum(nums, i + 1, i + 2, num_bits)
        } else {
            Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, num_bits)
                + Solution::total_diff_bit_sum(nums, i, j + 1, num_bits)
        }
    }

    proof fn total_hamming_distance_spec_add_acc(nums: Seq<i32>, i: nat, j: nat, acc: nat)
        ensures
            Solution::total_hamming_distance_spec(nums, i, j, acc)
                == Solution::total_hamming_distance_spec(nums, i, j, 0) + acc,
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::total_hamming_distance_spec_add_acc(nums, i + 1, i + 2, acc);
        } else {
            let dist = Solution::hamming_distance_spec((nums[i as int] ^ nums[j as int]) as nat);
            Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1, acc + dist);
            Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1, dist);
        }
    }

    proof fn lemma_total_eq_total_diff(nums: Seq<i32>, i: nat, j: nat, num_bits: nat)
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] < Solution::pow2(num_bits) as int,
            forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, i, j, 0) == Solution::total_diff_bit_sum(nums, i, j, num_bits),
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::lemma_total_eq_total_diff(nums, i + 1, i + 2, num_bits);
        } else {
            Solution::lemma_total_eq_total_diff(nums, i, j + 1, num_bits);
            let a = nums[i as int] as nat;
            let b = nums[j as int] as nat;
            let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
            Solution::lemma_hamming_eq_diff_bit_sum(a, b, xor_val, num_bits);
            let dist = Solution::hamming_distance_spec(xor_val);
            Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1, dist);
        }
    }

    pub open spec fn bit_of(x: nat, b: nat) -> nat {
        (x / Solution::pow2(b)) % 2
    }

    proof fn lemma_div_compose(a: nat, p: nat)
        requires
            p >= 1,
        ensures
            a / (2 * p) == (a / 2) / p,
    {
        assert(a / (2 * p) == (a / 2) / p) by (nonlinear_arith)
            requires
                p >= 1;
    }

    proof fn lemma_bit_of_step(x: nat, b: nat)
        ensures
            Solution::bit_of(x, b + 1) == Solution::bit_of(x / 2, b),
    {
        Solution::lemma_pow2_pos(b);
        assert(Solution::pow2(b + 1) == 2 * Solution::pow2(b));
        Solution::lemma_div_compose(x, Solution::pow2(b));
        assert(x / Solution::pow2(b + 1) == (x / 2) / Solution::pow2(b));
    }

    proof fn lemma_diff_bit_sum_step(a: nat, b: nat, k: nat)
        requires
            k >= 1,
        ensures
            Solution::diff_bit_sum(a, b, k) == Solution::diff_bit_sum(a, b, (k - 1) as nat)
                + (if Solution::bit_of(a, (k - 1) as nat) != Solution::bit_of(b, (k - 1) as nat) { 1nat } else { 0nat }),
        decreases k,
    {
        let m: nat = (k - 1) as nat;
        if m == 0 {
            assert(Solution::pow2(0) == 1);
            assert(Solution::bit_of(a, 0) == a % 2);
            assert(Solution::bit_of(b, 0) == b % 2);
        } else {
            Solution::lemma_diff_bit_sum_step(a / 2, b / 2, m);
            Solution::lemma_bit_of_step(a, (m - 1) as nat);
            Solution::lemma_bit_of_step(b, (m - 1) as nat);
            let d0: nat = if (a % 2) != (b % 2) { 1nat } else { 0nat };
            assert(Solution::diff_bit_sum(a, b, k) == d0 + Solution::diff_bit_sum(a / 2, b / 2, m));
            assert(Solution::diff_bit_sum(a, b, m) == d0 + Solution::diff_bit_sum(a / 2, b / 2, (m - 1) as nat));
            assert(Solution::diff_bit_sum(a / 2, b / 2, m) == Solution::diff_bit_sum(a / 2, b / 2, (m - 1) as nat)
                + (if Solution::bit_of(a / 2, (m - 1) as nat) != Solution::bit_of(b / 2, (m - 1) as nat) { 1nat } else { 0nat }));
            assert(Solution::bit_of(a, m) == Solution::bit_of(a / 2, (m - 1) as nat));
            assert(Solution::bit_of(b, m) == Solution::bit_of(b / 2, (m - 1) as nat));
        }
    }

    pub open spec fn count_bit_set_upto(nums: Seq<i32>, b: nat, upto: nat) -> nat
        decreases upto
    {
        if upto == 0 { 0 }
        else {
            let prev = Solution::count_bit_set_upto(nums, b, (upto - 1) as nat);
            if Solution::bit_of(nums[upto as int - 1] as nat, b) == 1 { prev + 1 } else { prev }
        }
    }

    pub open spec fn pairs_differ_at_bit(nums: Seq<i32>, i: nat, j: nat, b: nat) -> nat
        decreases nums.len() - i, nums.len() - j
    {
        if i >= nums.len() {
            0
        } else if j >= nums.len() {
            Solution::pairs_differ_at_bit(nums, i + 1, i + 2, b)
        } else {
            let d = if Solution::bit_of(nums[i as int] as nat, b) != Solution::bit_of(nums[j as int] as nat, b) { 1nat } else { 0nat };
            d + Solution::pairs_differ_at_bit(nums, i, j + 1, b)
        }
    }

    proof fn lemma_total_diff_bit_sum_step(nums: Seq<i32>, i: nat, j: nat, k: nat)
        requires
            k >= 1,
        ensures
            Solution::total_diff_bit_sum(nums, i, j, k)
                == Solution::total_diff_bit_sum(nums, i, j, (k - 1) as nat)
                    + Solution::pairs_differ_at_bit(nums, i, j, (k - 1) as nat),
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::lemma_total_diff_bit_sum_step(nums, i + 1, i + 2, k);
        } else {
            Solution::lemma_total_diff_bit_sum_step(nums, i, j + 1, k);
            Solution::lemma_diff_bit_sum_step(nums[i as int] as nat, nums[j as int] as nat, k);
            let m: nat = (k - 1) as nat;
            let d = if Solution::bit_of(nums[i as int] as nat, m) != Solution::bit_of(nums[j as int] as nat, m) { 1nat } else { 0nat };
            assert(Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, k)
                == Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, m) + d);
            assert(Solution::total_diff_bit_sum(nums, i, j, k)
                == Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, k)
                    + Solution::total_diff_bit_sum(nums, i, j + 1, k));
            assert(Solution::total_diff_bit_sum(nums, i, j, m)
                == Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, m)
                    + Solution::total_diff_bit_sum(nums, i, j + 1, m));
            assert(Solution::pairs_differ_at_bit(nums, i, j, m)
                == d + Solution::pairs_differ_at_bit(nums, i, j + 1, m));
        }
    }

    pub open spec fn count_diff_from(nums: Seq<i32>, i: nat, j: nat, b: nat) -> nat
        decreases nums.len() - j
    {
        if j >= nums.len() {
            0
        } else {
            let d = if Solution::bit_of(nums[j as int] as nat, b) != Solution::bit_of(nums[i as int] as nat, b) { 1nat } else { 0nat };
            d + Solution::count_diff_from(nums, i, j + 1, b)
        }
    }

    proof fn lemma_pairs_differ_row(nums: Seq<i32>, i: nat, j: nat, b: nat)
        requires
            i < nums.len(),
            i < j,
            j <= nums.len(),
        ensures
            Solution::pairs_differ_at_bit(nums, i, j, b)
                == Solution::count_diff_from(nums, i, j, b) + Solution::pairs_differ_at_bit(nums, i + 1, i + 2, b),
        decreases nums.len() - j,
    {
        if j >= nums.len() {
        } else {
            Solution::lemma_pairs_differ_row(nums, i, j + 1, b);
        }
    }

    pub open spec fn count_diff_from_countable(nums: Seq<i32>, b: nat, a: nat, c: nat) -> nat
        decreases c - a when a <= c
    {
        if a >= c {
            0
        } else {
            (if Solution::bit_of(nums[a as int] as nat, b) == 1 { 1nat } else { 0nat })
                + Solution::count_diff_from_countable(nums, b, (a + 1) as nat, c)
        }
    }

    proof fn lemma_count_bit_set_upto_step(nums: Seq<i32>, b: nat, upto: nat)
        requires
            upto < nums.len(),
        ensures
            Solution::count_bit_set_upto(nums, b, upto + 1) == Solution::count_bit_set_upto(nums, b, upto)
                + (if Solution::bit_of(nums[upto as int] as nat, b) == 1 { 1nat } else { 0nat }),
    {
    }

    proof fn lemma_count_bit_set_additive(nums: Seq<i32>, b: nat, a: nat, c: nat)
        requires
            a <= c <= nums.len(),
        ensures
            Solution::count_bit_set_upto(nums, b, c)
                == Solution::count_bit_set_upto(nums, b, a) + Solution::count_diff_from_countable(nums, b, a, c),
        decreases c - a,
    {
        if a >= c {
        } else {
            Solution::lemma_count_bit_set_additive(nums, b, (a + 1) as nat, c);
            Solution::lemma_count_bit_set_upto_step(nums, b, a);
        }
    }

    proof fn lemma_count_diff_from_formula(nums: Seq<i32>, i: nat, j: nat, b: nat)
        requires
            i < nums.len(),
            j <= nums.len(),
        ensures
            Solution::bit_of(nums[i as int] as nat, b) == 1 ==>
                Solution::count_diff_from(nums, i, j, b)
                    == (nums.len() - j) - Solution::count_diff_from_countable(nums, b, j, nums.len()),
            Solution::bit_of(nums[i as int] as nat, b) == 0 ==>
                Solution::count_diff_from(nums, i, j, b)
                    == Solution::count_diff_from_countable(nums, b, j, nums.len()),
        decreases nums.len() - j,
    {
        if j >= nums.len() {
        } else {
            Solution::lemma_count_diff_from_formula(nums, i, j + 1, b);
            let nj = nums[j as int] as nat;
            let d: nat = if Solution::bit_of(nj, b) != Solution::bit_of(nums[i as int] as nat, b) { 1nat } else { 0nat };
            assert(Solution::count_diff_from(nums, i, j, b) == d + Solution::count_diff_from(nums, i, j + 1, b));
            assert(Solution::count_diff_from_countable(nums, b, j, nums.len())
                == (if Solution::bit_of(nj, b) == 1 { 1nat } else { 0nat })
                    + Solution::count_diff_from_countable(nums, b, (j + 1) as nat, nums.len()));
        }
    }

    proof fn lemma_count_diff_from_countable_bound(nums: Seq<i32>, b: nat, a: nat, c: nat)
        requires
            a <= c,
        ensures
            Solution::count_diff_from_countable(nums, b, a, c) <= c - a,
        decreases c - a,
    {
        if a >= c {
        } else {
            Solution::lemma_count_diff_from_countable_bound(nums, b, (a + 1) as nat, c);
        }
    }

    proof fn lemma_pairs_differ_combinatorial(nums: Seq<i32>, i: nat, b: nat)
        requires
            i <= nums.len(),
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k],
        ensures
            Solution::pairs_differ_at_bit(nums, i, (i + 1) as nat, b)
                == Solution::count_diff_from_countable(nums, b, i, nums.len())
                    * ((nums.len() - i) - Solution::count_diff_from_countable(nums, b, i, nums.len())),
        decreases nums.len() - i,
    {
        if i >= nums.len() {
            assert(Solution::pairs_differ_at_bit(nums, i, (i + 1) as nat, b) == 0);
            assert(Solution::count_diff_from_countable(nums, b, i, nums.len()) == 0);
        } else {
            let i1: nat = (i + 1) as nat;
            let i2: nat = (i + 2) as nat;
            Solution::lemma_pairs_differ_combinatorial(nums, i1, b);
            Solution::lemma_pairs_differ_row(nums, i, i1, b);
            Solution::lemma_count_diff_from_formula(nums, i, i1, b);
            let ones_i1: nat = Solution::count_diff_from_countable(nums, b, i1, nums.len());
            let ones_i: nat = Solution::count_diff_from_countable(nums, b, i, nums.len());
            Solution::lemma_count_diff_from_countable_bound(nums, b, i1, nums.len());
            Solution::lemma_count_diff_from_countable_bound(nums, b, i, nums.len());
            assert(nums[i as int] >= 0);
            let bit_i: nat = Solution::bit_of(nums[i as int] as nat, b);
            let n: int = nums.len() as int;
            let zeros_i1: int = (n - i - 1) - ones_i1 as int;
            let zeros_i: int = (n - i) - ones_i as int;
            let cd: nat = Solution::count_diff_from(nums, i, i1, b);
            let pdi: nat = Solution::pairs_differ_at_bit(nums, i, i1, b);
            let pdi1: nat = Solution::pairs_differ_at_bit(nums, i1, i2, b);
            assert(pdi == cd + pdi1);
            assert(Solution::pairs_differ_at_bit(nums, i1, (i1 + 1) as nat, b)
                == Solution::count_diff_from_countable(nums, b, i1, nums.len())
                    * ((nums.len() - i1) - Solution::count_diff_from_countable(nums, b, i1, nums.len())));
            assert(i1 + 1 == i2);
            assert(zeros_i1 as nat == (nums.len() - i1) - ones_i1) by (nonlinear_arith)
                requires
                    zeros_i1 == (n - i - 1) - ones_i1 as int,
                    n == nums.len() as int,
                    i1 == i + 1,
                    i < nums.len(),
                    ones_i1 <= nums.len() - i1;
            assert(pdi1 == ones_i1 * (zeros_i1 as nat));
            assert(bit_i == 1 ==> cd == (zeros_i1 as nat));
            assert(bit_i == 0 ==> cd == ones_i1);
            assert(bit_i == 1 ==> ones_i == 1 + ones_i1);
            assert(bit_i == 0 ==> ones_i == ones_i1);
            assert(bit_i == 0 || bit_i == 1);
            assert(pdi as int == ones_i as int * zeros_i) by (nonlinear_arith)
                requires
                    pdi as int == cd as int + pdi1 as int,
                    pdi1 as int == ones_i1 as int * zeros_i1,
                    bit_i == 1 ==> cd as int == zeros_i1,
                    bit_i == 0 ==> cd as int == ones_i1 as int,
                    bit_i == 1 ==> ones_i as int == 1 + ones_i1 as int,
                    bit_i == 0 ==> ones_i as int == ones_i1 as int,
                    zeros_i1 == (n - i - 1) - ones_i1 as int,
                    zeros_i == (n - i) - ones_i as int,
                    bit_i == 0 || bit_i == 1;
            assert(zeros_i >= 0) by (nonlinear_arith)
                requires
                    zeros_i == (n - i) - ones_i as int,
                    n == nums.len() as int,
                    ones_i <= nums.len() - i;
            assert(zeros_i as nat == (nums.len() - i) - ones_i) by (nonlinear_arith)
                requires
                    zeros_i == (n - i) - ones_i as int,
                    n == nums.len() as int,
                    ones_i <= nums.len() - i,
                    zeros_i >= 0;
            assert(pdi == ones_i * (zeros_i as nat)) by (nonlinear_arith)
                requires
                    pdi as int == ones_i as int * zeros_i,
                    zeros_i >= 0;
            assert(pdi == ones_i * ((nums.len() - i) - ones_i));
        }
    }

    proof fn lemma_total_diff_bit_sum_zero(nums: Seq<i32>, i: nat, j: nat)
        ensures
            Solution::total_diff_bit_sum(nums, i, j, 0) == 0,
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::lemma_total_diff_bit_sum_zero(nums, i + 1, i + 2);
        } else {
            Solution::lemma_total_diff_bit_sum_zero(nums, i, j + 1);
            assert(Solution::diff_bit_sum(nums[i as int] as nat, nums[j as int] as nat, 0) == 0);
        }
    }

    pub open spec fn bit_formula_sum(nums: Seq<i32>, num_bits: nat) -> nat
        decreases num_bits
    {
        if num_bits == 0 {
            0
        } else {
            let ones = Solution::count_bit_set_upto(nums, (num_bits - 1) as nat, nums.len());
            (Solution::bit_formula_sum(nums, (num_bits - 1) as nat) + ones * (nums.len() - ones)) as nat
        }
    }

    proof fn lemma_total_diff_bit_sum_eq_formula(nums: Seq<i32>, num_bits: nat)
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k],
        ensures
            Solution::total_diff_bit_sum(nums, 0, 1, num_bits) == Solution::bit_formula_sum(nums, num_bits),
        decreases num_bits,
    {
        if num_bits == 0 {
            Solution::lemma_total_diff_bit_sum_zero(nums, 0, 1);
            assert(Solution::bit_formula_sum(nums, 0) == 0);
        } else {
            let m: nat = (num_bits - 1) as nat;
            Solution::lemma_total_diff_bit_sum_eq_formula(nums, m);
            Solution::lemma_total_diff_bit_sum_step(nums, 0, 1, num_bits);
            Solution::lemma_pairs_differ_combinatorial(nums, 0, m);
            Solution::lemma_count_bit_set_additive(nums, m, 0, nums.len());
            let ones = Solution::count_bit_set_upto(nums, m, nums.len());
            assert(Solution::count_diff_from_countable(nums, m, 0, nums.len()) == ones);
            assert(Solution::pairs_differ_at_bit(nums, 0, 1, m) == ones * (nums.len() - ones));
            assert(Solution::total_diff_bit_sum(nums, 0, 1, num_bits)
                == Solution::total_diff_bit_sum(nums, 0, 1, m) + Solution::pairs_differ_at_bit(nums, 0, 1, m));
            assert(Solution::bit_formula_sum(nums, num_bits)
                == Solution::bit_formula_sum(nums, m) + ones * (nums.len() - ones));
            assert(Solution::total_diff_bit_sum(nums, 0, 1, num_bits) == Solution::bit_formula_sum(nums, num_bits));
        }
    }

    proof fn lemma_total_hamming_eq_bit_formula(nums: Seq<i32>, num_bits: nat)
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] < Solution::pow2(num_bits) as int,
            forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, 0, 1, 0) == Solution::bit_formula_sum(nums, num_bits),
    {
        Solution::lemma_total_eq_total_diff(nums, 0, 1, num_bits);
        Solution::lemma_total_diff_bit_sum_eq_formula(nums, num_bits);
    }

    proof fn lemma_count_bit_set_upto_bound(nums: Seq<i32>, b: nat, upto: nat)
        requires
            upto <= nums.len(),
        ensures
            Solution::count_bit_set_upto(nums, b, upto) <= upto,
        decreases upto,
    {
        if upto > 0 {
            Solution::lemma_count_bit_set_upto_bound(nums, b, (upto - 1) as nat);
        }
    }

    proof fn lemma_pow2_mono(e1: nat, e2: nat)
        requires
            e1 <= e2,
        ensures
            Solution::pow2(e1) <= Solution::pow2(e2),
        decreases e2 - e1,
    {
        if e1 < e2 {
            Solution::lemma_pow2_mono(e1, (e2 - 1) as nat);
            Solution::lemma_pow2_pos((e2 - 1) as nat);
            assert(Solution::pow2(e2) == 2 * Solution::pow2((e2 - 1) as nat));
        }
    }

    proof fn lemma_pow2_30()
        ensures
            Solution::pow2(30) == 1073741824,
    {
        assert(Solution::pow2(0) == 1);
        assert(Solution::pow2(1) == 2 * Solution::pow2(0));
        assert(Solution::pow2(2) == 2 * Solution::pow2(1));
        assert(Solution::pow2(3) == 2 * Solution::pow2(2));
        assert(Solution::pow2(4) == 2 * Solution::pow2(3));
        assert(Solution::pow2(5) == 2 * Solution::pow2(4));
        assert(Solution::pow2(6) == 2 * Solution::pow2(5));
        assert(Solution::pow2(7) == 2 * Solution::pow2(6));
        assert(Solution::pow2(8) == 2 * Solution::pow2(7));
        assert(Solution::pow2(9) == 2 * Solution::pow2(8));
        assert(Solution::pow2(10) == 2 * Solution::pow2(9));
        assert(Solution::pow2(11) == 2 * Solution::pow2(10));
        assert(Solution::pow2(12) == 2 * Solution::pow2(11));
        assert(Solution::pow2(13) == 2 * Solution::pow2(12));
        assert(Solution::pow2(14) == 2 * Solution::pow2(13));
        assert(Solution::pow2(15) == 2 * Solution::pow2(14));
        assert(Solution::pow2(16) == 2 * Solution::pow2(15));
        assert(Solution::pow2(17) == 2 * Solution::pow2(16));
        assert(Solution::pow2(18) == 2 * Solution::pow2(17));
        assert(Solution::pow2(19) == 2 * Solution::pow2(18));
        assert(Solution::pow2(20) == 2 * Solution::pow2(19));
        assert(Solution::pow2(21) == 2 * Solution::pow2(20));
        assert(Solution::pow2(22) == 2 * Solution::pow2(21));
        assert(Solution::pow2(23) == 2 * Solution::pow2(22));
        assert(Solution::pow2(24) == 2 * Solution::pow2(23));
        assert(Solution::pow2(25) == 2 * Solution::pow2(24));
        assert(Solution::pow2(26) == 2 * Solution::pow2(25));
        assert(Solution::pow2(27) == 2 * Solution::pow2(26));
        assert(Solution::pow2(28) == 2 * Solution::pow2(27));
        assert(Solution::pow2(29) == 2 * Solution::pow2(28));
        assert(Solution::pow2(30) == 2 * Solution::pow2(29));
    }

    proof fn lemma_bit_extract(x: i32, pw: i64, b: nat)
        requires
            0 <= x,
            pw as int == Solution::pow2(b) as int,
        ensures
            ((x as i64 / pw) % 2 == 1) == (Solution::bit_of(x as nat, b) == 1),
    {
        Solution::lemma_pow2_pos(b);
        assert(Solution::bit_of(x as nat, b) == (x as nat / Solution::pow2(b)) % 2);
        assert(pw >= 1);
        let qi: i64 = (x as i64 / pw) as i64;
        let qn: nat = x as nat / Solution::pow2(b);
        assert(qi as int == (x as nat as int) / (Solution::pow2(b) as int)) by (nonlinear_arith)
            requires
                0 <= x,
                pw as int == Solution::pow2(b) as int,
                pw >= 1,
                qi as int == (x as int) / (pw as int);
        assert(qn as int == (x as nat as int) / (Solution::pow2(b) as int)) by (nonlinear_arith)
            requires
                0 <= x,
                Solution::pow2(b) >= 1,
                qn == x as nat / Solution::pow2(b);
        assert(qi as int == qn as int);
        assert(qi >= 0);
        assert((qi % 2 == 1) == (qn % 2 == 1)) by (nonlinear_arith)
            requires
                qi as int == qn as int,
                qi >= 0;
    }

    pub fn total_hamming_distance(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            i32::MIN <= Solution::total_hamming_distance_spec(nums@, 0, 1, 0) <= i32::MAX,
        ensures
            res == Solution::total_hamming_distance_spec(nums@, 0, 1, 0),
    {
        let n = nums.len();
        let mut total: i64 = 0;
        let mut pw: i64 = 1;
        let mut b: usize = 0;
        proof {
            assert(Solution::pow2(0) == 1);
        }
        while b < 30
            invariant
                0 <= b <= 30,
                n == nums.len(),
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] nums[k as int] <= 1_000_000_000,
                pw as int == Solution::pow2(b as nat) as int,
                pw >= 1,
                total as int == Solution::bit_formula_sum(nums@, b as nat),
                0 <= total <= (b as i64) * 100_000_000,
                n <= 10000,
            decreases 30 - b,
        {
            let mut ones: i64 = 0;
            let mut idx: usize = 0;
            while idx < n
                invariant
                    0 <= idx <= n,
                    n == nums.len(),
                    n <= 10000,
                    forall|k: int| 0 <= k < n ==> 0 <= #[trigger] nums[k as int] <= 1_000_000_000,
                    pw as int == Solution::pow2(b as nat) as int,
                    pw >= 1,
                    ones as int == Solution::count_bit_set_upto(nums@, b as nat, idx as nat),
                decreases n - idx,
            {
                proof {
                    Solution::lemma_bit_extract(nums@[idx as int], pw, b as nat);
                    Solution::lemma_count_bit_set_upto_bound(nums@, b as nat, idx as nat);
                    assert(Solution::count_bit_set_upto(nums@, b as nat, idx as nat) <= idx);
                    assert(ones as int <= idx as int);
                    assert(ones <= idx as i64);
                }
                if (nums[idx] as i64 / pw) % 2 == 1 {
                    ones += 1;
                }
                idx += 1;
                proof {
                    assert(Solution::count_bit_set_upto(nums@, b as nat, idx as nat)
                        == Solution::count_bit_set_upto(nums@, b as nat, (idx - 1) as nat)
                            + (if Solution::bit_of(nums[idx as int - 1] as nat, b as nat) == 1 { 1nat } else { 0nat }));
                }
            }
            proof {
                Solution::lemma_count_bit_set_upto_bound(nums@, b as nat, n as nat);
                assert(Solution::count_bit_set_upto(nums@, b as nat, n as nat) <= n);
                assert(ones as int == Solution::count_bit_set_upto(nums@, b as nat, n as nat));
                assert(n as nat == nums@.len());
                assert(Solution::bit_formula_sum(nums@, (b + 1) as nat)
                    == Solution::bit_formula_sum(nums@, b as nat)
                        + Solution::count_bit_set_upto(nums@, b as nat, nums@.len()) as nat
                            * ((nums@.len() - Solution::count_bit_set_upto(nums@, b as nat, nums@.len())) as nat));
                assert(Solution::bit_formula_sum(nums@, (b + 1) as nat)
                    == Solution::bit_formula_sum(nums@, b as nat) + (ones as nat) * ((n - ones) as nat));
                assert(0 <= ones as int <= n as int);
                assert(0 <= ones <= n as i64);
                assert(ones * ((n as i64) - ones) <= 100_000_000) by (nonlinear_arith)
                    requires
                        0 <= ones <= n as i64,
                        n as i64 <= 10000;
            }
            total += ones * ((n as i64) - ones);
            proof {
                Solution::lemma_pow2_mono(b as nat, 29);
                Solution::lemma_pow2_30();
                assert(Solution::pow2(30) == 2 * Solution::pow2(29));
                assert(Solution::pow2(29) == 536870912);
                assert(pw as int <= 536870912);
            }
            pw *= 2;
            b += 1;
            proof {
                assert(Solution::pow2(b as nat) == 2 * Solution::pow2((b - 1) as nat));
            }
        }
        proof {
            Solution::lemma_pow2_30();
            assert(forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums@[k] < Solution::pow2(30) as int);
            assert(forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums@[k] <= i32::MAX);
            Solution::lemma_total_hamming_eq_bit_formula(nums@, 30);
        }
        total as i32
    }

}

}
