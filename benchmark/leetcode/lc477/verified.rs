use vstd::arithmetic::logarithm::{
    lemma_log0, lemma_log_is_ordered, lemma_log_nonnegative, lemma_log_pow, lemma_log_s, log,
};
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::{lemma2_to64, lemma_pow2, pow2};
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

    pub proof fn lemma_xor_nonneg(a: i32, b: i32)
        requires
            0 <= a <= i32::MAX,
            0 <= b <= i32::MAX,
        ensures
            (a ^ b) >= 0,
    {
        assert(a ^ b >= 0) by(bit_vector)
            requires
                0 <= a <= i32::MAX,
                0 <= b <= i32::MAX;
    }

    pub open spec fn hamming_distance_spec(xor_result: nat) -> nat {
        Solution::hamming_distance_spec_helper(xor_result, 0)
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

    pub proof fn hamming_distance_bound(x: nat, a: nat)
        ensures
            Solution::hamming_distance_spec_helper(x, a) <= a + log(2, x as int) + 1,
        decreases x,
    {
        Solution::hamming_distance_properties(x, a);
        if x < 2 {
            lemma_log0(2, x as int);
        } else {
            lemma_log_s(2, x as int);
            lemma_log_nonnegative(2, (x / 2) as int);
            Solution::hamming_distance_bound(x / 2, a + (x % 2));
        }
    }

    pub proof fn hamming_distance_bound_i32(x: nat)
        requires
            x <= pow2(31),
        ensures
            Solution::hamming_distance_spec_helper(x, 0) <= 32,
    {
        lemma_pow2(31);
        lemma_log_pow(2, 31);
        lemma_log_is_ordered(2, x as int, pow2(31) as int);
        Solution::hamming_distance_bound(x, 0);
    }

    pub proof fn hamming_distance_properties(x: nat, a: nat)
        ensures
            Solution::hamming_distance_spec_helper(x, a) == Solution::hamming_distance_spec_helper(
                x / 2,
                a + (x % 2),
            ),
            Solution::hamming_distance_spec_helper(x, a) >= a,
        decreases x,
    {
        if x == 0 {
        } else {
            let ones = x % 2;
            let new_acc = a + ones;

            Solution::hamming_distance_properties(x / 2, new_acc);
        }
    }

    pub proof fn total_hamming_distance_spec_add_acc(
        nums: Seq<i32>,
        i: nat,
        j: nat,
        acc: nat,
    )
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
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

    pub open spec fn remaining_pairs(n: nat, i: nat, j: nat) -> nat
        decreases n - i, n - j,
    {
        if i >= n {
            0
        } else if j >= n {
            Solution::remaining_pairs(n, i + 1, i + 2)
        } else {
            1 + Solution::remaining_pairs(n, i, j + 1)
        }
    }

    pub proof fn lemma_total_hamming_distance_upper_bound(
        nums: Seq<i32>,
        i: nat,
        j: nat,
    )
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, i, j, 0)
                <= 32 * Solution::remaining_pairs(nums.len() as nat, i, j),
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::lemma_total_hamming_distance_upper_bound(nums, i + 1, i + 2);
            Solution::total_hamming_distance_spec_add_acc(nums, i + 1, i + 2, 0);
        } else {
            let xor_val = (nums[i as int] ^ nums[j as int]) as nat;
            let dist = Solution::hamming_distance_spec(xor_val);
            Self::lemma_xor_nonneg(nums[i as int], nums[j as int]);
            lemma2_to64();
            Solution::hamming_distance_bound_i32(xor_val);
            Solution::lemma_total_hamming_distance_upper_bound(nums, i, j + 1);
            Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1, dist);
        }
    }

    pub proof fn lemma_remaining_pairs_bound(n: nat, i: nat, j: nat)
        requires
            i < n,
            j == i + 1,
        ensures
            Solution::remaining_pairs(n, i, j)
                <= (n - i) * (n - i) / 2,
        decreases n - i,
    {

        Solution::lemma_remaining_pairs_inner(n, i, j);
        if i + 1 < n {
            Solution::lemma_remaining_pairs_bound(n, i + 1, i + 2);
            let m = (n - i) as int;
            assert((m - 1) + (m - 1) * (m - 1) / 2 <= m * m / 2) by(nonlinear_arith)
                requires m >= 2;
        }
    }

    pub proof fn lemma_remaining_pairs_inner(n: nat, i: nat, j: nat)
        requires
            i < n,
            i < j,
            j <= n,
        ensures
            Solution::remaining_pairs(n, i, j)
                == (n - j) + Solution::remaining_pairs(n, i + 1, i + 2),
        decreases n - j,
    {
        if j >= n {
        } else {
            Solution::lemma_remaining_pairs_inner(n, i, j + 1);
        }
    }

    pub proof fn lemma_total_hamming_distance_nonneg(
        nums: Seq<i32>,
        i: nat,
        j: nat,
    )
        requires
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, i, j, 0) >= 0,
        decreases nums.len() - i, nums.len() - j,
    {
        if i >= nums.len() {
        } else if j >= nums.len() {
            Solution::lemma_total_hamming_distance_nonneg(nums, i + 1, i + 2);
            Solution::total_hamming_distance_spec_add_acc(nums, i + 1, i + 2, 0);
        } else {
            Solution::lemma_total_hamming_distance_nonneg(nums, i, j + 1);
            Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1,
                Solution::hamming_distance_spec((nums[i as int] ^ nums[j as int]) as nat));
        }
    }

    pub proof fn lemma_total_fits_i32(nums: Seq<i32>)
        requires
            1 <= nums.len() <= 10000,
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, 0, 1, 0) <= i32::MAX,
    {
        let n = nums.len() as nat;
        Solution::lemma_total_hamming_distance_upper_bound(nums, 0, 1);
        if n >= 2 {
            Solution::lemma_remaining_pairs_bound(n, 0, 1);
            assert(32 * (n * n / 2) <= i32::MAX) by(nonlinear_arith)
                requires n <= 10000;
        } else {
            assert(Solution::remaining_pairs(n, 1, 2) == 0);
            assert(Solution::remaining_pairs(n, 0, 1) == 0);
        }
    }

    pub proof fn total_hamming_distance_spec_unfold(
        nums: Seq<i32>,
        i: nat,
        j: nat,
    )
        requires
            i < nums.len(),
            j < nums.len(),
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
        ensures
            Solution::total_hamming_distance_spec(nums, i, j, 0)
                == Solution::hamming_distance_spec((nums[i as int] ^ nums[j as int]) as nat)
                + Solution::total_hamming_distance_spec(nums, i, j + 1, 0),
        decreases nums.len() - i, nums.len() - j,
    {
        let dist = Solution::hamming_distance_spec((nums[i as int] ^ nums[j as int]) as nat);
        Solution::total_hamming_distance_spec_add_acc(nums, i, j + 1, dist);
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn total_hamming_distance(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX,
            i32::MIN <= Solution::total_hamming_distance_spec(nums@, 0, 1, 0) <= i32::MAX,
        ensures
            res == Solution::total_hamming_distance_spec(nums@, 0, 1, 0),
    {
        let n = nums.len();
        let ghost nums_seq = nums@;
        let mut total = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 10000,
                n == nums.len(),
                nums_seq == nums@,
                forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
                total == Solution::total_hamming_distance_spec(nums_seq, 0, 1, 0) - Solution::total_hamming_distance_spec(
                    nums_seq,
                    i as nat,
                    (i + 1) as nat,
                    0,
                ),
        {
            let mut j = i + 1;
            let ghost i_val = i;

            while j < n
                invariant
                    0 <= i < n,
                    i < j <= n,
                    1 <= n <= 10000,
                    n == nums.len(),
                    nums_seq == nums@,
                    i_val == i,
                    forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
                    total == Solution::total_hamming_distance_spec(nums_seq, 0, 1, 0) - Solution::total_hamming_distance_spec(
                        nums_seq,
                        i as nat,
                        j as nat,
                        0,
                    ),
            {
                proof {
                    Self::lemma_xor_nonneg(nums[i as int], nums[j as int]);
                    lemma2_to64();
                    Solution::hamming_distance_bound_i32((nums[i as int] ^ nums[j as int]) as nat);
                }
                let mut xor = (nums[i] ^ nums[j]) as u32;
                let mut count: u32 = 0;

                while xor != 0
                    invariant
                        0 <= i < n,
                        i < j < n,
                        n == nums.len(),
                        nums_seq == nums@,
                        forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= i32::MAX,
                        (nums[i as int] ^ nums[j as int]) >= 0,
                        Solution::hamming_distance_spec_helper(xor as nat, count as nat)
                            == Solution::hamming_distance_spec((nums[i as int] ^ nums[j as int]) as nat),
                    decreases xor,
                {
                    proof {
                        lemma2_to64();
                        Solution::hamming_distance_bound_i32((nums[i as int] ^ nums[j as int]) as nat);
                        Solution::hamming_distance_properties(xor as nat, count as nat);
                    }
                    count += (xor % 2);
                    xor /= 2;
                }

                proof {
                    Solution::total_hamming_distance_spec_unfold(nums_seq, i as nat, j as nat);
                    Solution::lemma_total_hamming_distance_nonneg(nums_seq, i as nat, (j + 1) as nat);
                    Solution::lemma_total_fits_i32(nums_seq);
                }
                total += count as i32;
                j += 1;
            }

            i += 1;
        }

        total
    }
}

} 
