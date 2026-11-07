use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {

    pub open spec fn segment_product(nums: Seq<i32>, i: int, j: int) -> int
        decreases j - i,
    {
        if i > j {
            1
        } else if i == j {
            nums[i] as int
        } else {
            (nums[i] as int) * Self::segment_product(nums, i + 1, j)
        }
    }

    pub open spec fn count_product_less(nums: Seq<i32>, k: int, i: int, n: int) -> int
        decreases n - i,
    {
        if i >= n {
            0
        } else {
            Self::num_ends(nums, k, i, i, n) + Self::count_product_less(nums, k, i + 1, n)
        }
    }

    pub open spec fn num_ends(nums: Seq<i32>, k: int, i: int, j: int, n: int) -> int
        decreases n - j,
    {
        if j >= n {
            0
        } else if Self::segment_product(nums, i, j) < k {
            1 + Self::num_ends(nums, k, i, j + 1, n)
        } else {
            0
        }
    }

    pub open spec fn num_ends_upto(nums: Seq<i32>, k: int, i: int, j: int, R: int) -> int
        decreases R - j,
    {
        if j >= R {
            0
        } else if Self::segment_product(nums, i, j) < k {
            1 + Self::num_ends_upto(nums, k, i, j + 1, R)
        } else {
            0
        }
    }

    pub open spec fn count_upto(nums: Seq<i32>, k: int, i: int, n: int, R: int) -> int
        decreases n - i,
    {
        if i >= n {
            0
        } else {
            Self::num_ends_upto(nums, k, i, i, R) + Self::count_upto(nums, k, i + 1, n, R)
        }
    }

    proof fn lemma_segment_product_positive(nums: Seq<i32>, i: int, j: int, n: int)
        requires
            0 <= i, j < n, n <= nums.len(),
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
        ensures
            Self::segment_product(nums, i, j) >= 1,
        decreases j - i,
    {
        if i > j {
        } else if i == j {
        } else {
            Self::lemma_segment_product_positive(nums, i + 1, j, n);
            assert((nums[i] as int) * Self::segment_product(nums, i + 1, j) >= 1)
                by(nonlinear_arith)
                requires (nums[i] as int) >= 1, Self::segment_product(nums, i + 1, j) >= 1;
        }
    }

    proof fn lemma_segment_product_append(nums: Seq<i32>, i: int, j: int, n: int)
        requires
            0 <= i, i <= j, j < n, n <= nums.len(),
        ensures
            Self::segment_product(nums, i, j) ==
                Self::segment_product(nums, i, j - 1) * (nums[j] as int),
        decreases j - i,
    {
        if i == j {
            assert(Self::segment_product(nums, i, i - 1) == 1int);
            assert(Self::segment_product(nums, i, j)
                == Self::segment_product(nums, i, j - 1) * (nums[j] as int));
        } else {
            Self::lemma_segment_product_append(nums, i + 1, j, n);
            let sp_rest_j = Self::segment_product(nums, i + 1, j);
            let sp_rest_jm = Self::segment_product(nums, i + 1, j - 1);
            let nj = nums[j] as int;
            let ni = nums[i] as int;
            assert(sp_rest_j == sp_rest_jm * nj);
            assert(Self::segment_product(nums, i, j) == ni * sp_rest_j);
            assert(Self::segment_product(nums, i, j) == ni * sp_rest_jm * nj)
                by(nonlinear_arith)
                requires
                    sp_rest_j == sp_rest_jm * nj,
                    Self::segment_product(nums, i, j) == ni * sp_rest_j;
            if i + 1 < j {
                assert(Self::segment_product(nums, i, j - 1) == ni * sp_rest_jm);
            } else {
                assert(sp_rest_jm == 1int);
                assert(Self::segment_product(nums, i, j - 1) == ni);
            }
            assert(Self::segment_product(nums, i, j)
                == Self::segment_product(nums, i, j - 1) * nj)
                by(nonlinear_arith)
                requires
                    Self::segment_product(nums, i, j) == ni * sp_rest_jm * nj,
                    Self::segment_product(nums, i, j - 1) == ni * sp_rest_jm;
        }
    }

    proof fn lemma_product_ge_chain(nums: Seq<i32>, i: int, j1: int, j2: int, n: int)
        requires
            0 <= i, i <= j1, j1 <= j2, j2 < n, n <= nums.len(),
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
        ensures
            Self::segment_product(nums, i, j2) >= Self::segment_product(nums, i, j1),
        decreases j2 - j1,
    {
        if j1 == j2 {
        } else {
            Self::lemma_product_ge_chain(nums, i, j1, j2 - 1, n);
            Self::lemma_segment_product_append(nums, i, j2, n);
            Self::lemma_segment_product_positive(nums, i, j2 - 1, n);
            assert(Self::segment_product(nums, i, j2)
                >= Self::segment_product(nums, i, j2 - 1))
                by(nonlinear_arith)
                requires
                    Self::segment_product(nums, i, j2)
                        == Self::segment_product(nums, i, j2 - 1) * (nums[j2] as int),
                    Self::segment_product(nums, i, j2 - 1) >= 1,
                    (nums[j2] as int) >= 1;
        }
    }

    proof fn lemma_product_mono_start(nums: Seq<i32>, i1: int, i2: int, j: int, n: int)
        requires
            0 <= i1, i1 <= i2, i2 <= j, j < n, n <= nums.len(),
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
        ensures
            Self::segment_product(nums, i2, j) <= Self::segment_product(nums, i1, j),
        decreases i2 - i1,
    {
        if i1 == i2 {
        } else {
            Self::lemma_product_mono_start(nums, i1 + 1, i2, j, n);
            Self::lemma_segment_product_positive(nums, i1 + 1, j, n);
            assert(Self::segment_product(nums, i1, j)
                >= Self::segment_product(nums, i1 + 1, j))
                by(nonlinear_arith)
                requires
                    Self::segment_product(nums, i1, j)
                        == (nums[i1] as int) * Self::segment_product(nums, i1 + 1, j),
                    Self::segment_product(nums, i1 + 1, j) >= 1,
                    (nums[i1] as int) >= 1;
        }
    }

    proof fn lemma_num_ends_upto_nonneg(nums: Seq<i32>, k: int, i: int, j: int, R: int)
        ensures Self::num_ends_upto(nums, k, i, j, R) >= 0,
        decreases R - j,
    {
        if j >= R {
        } else if Self::segment_product(nums, i, j) < k {
            Self::lemma_num_ends_upto_nonneg(nums, k, i, j + 1, R);
        } else {
        }
    }

    proof fn lemma_count_upto_nonneg(nums: Seq<i32>, k: int, i: int, n: int, R: int)
        ensures Self::count_upto(nums, k, i, n, R) >= 0,
        decreases n - i,
    {
        if i >= n {
        } else {
            Self::lemma_num_ends_upto_nonneg(nums, k, i, i, R);
            Self::lemma_count_upto_nonneg(nums, k, i + 1, n, R);
        }
    }

    proof fn lemma_k_le_1_count_zero(nums: Seq<i32>, k: int, i: int, n: int)
        requires
            k <= 1, 0 <= i, n <= nums.len(),
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
        ensures Self::count_product_less(nums, k, i, n) == 0,
        decreases n - i,
    {
        if i >= n {
        } else {
            Self::lemma_segment_product_positive(nums, i, i, n);
            Self::lemma_k_le_1_count_zero(nums, k, i + 1, n);
        }
    }

    proof fn lemma_num_ends_upto_eq(nums: Seq<i32>, k: int, i: int, j: int, n: int)
        ensures Self::num_ends_upto(nums, k, i, j, n) == Self::num_ends(nums, k, i, j, n),
        decreases n - j,
    {
        if j >= n {
        } else if Self::segment_product(nums, i, j) < k {
            Self::lemma_num_ends_upto_eq(nums, k, i, j + 1, n);
        } else {
        }
    }

    proof fn lemma_count_upto_eq(nums: Seq<i32>, k: int, i: int, n: int)
        requires i >= 0,
        ensures Self::count_upto(nums, k, i, n, n) == Self::count_product_less(nums, k, i, n),
        decreases n - i,
    {
        if i >= n {
        } else {
            Self::lemma_num_ends_upto_eq(nums, k, i, i, n);
            Self::lemma_count_upto_eq(nums, k, i + 1, n);
        }
    }

    proof fn lemma_count_upto_zero(nums: Seq<i32>, k: int, i: int, n: int)
        requires i >= 0,
        ensures Self::count_upto(nums, k, i, n, 0) == 0,
        decreases n - i,
    {
        if i >= n {
        } else {
            Self::lemma_count_upto_zero(nums, k, i + 1, n);
        }
    }

    proof fn lemma_num_ends_upto_step(nums: Seq<i32>, k: int, i: int, j: int, R: int, n: int)
        requires
            0 <= i, i <= j, j <= R, R < n, n <= nums.len(),
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
        ensures
            Self::num_ends_upto(nums, k, i, j, R + 1) ==
                Self::num_ends_upto(nums, k, i, j, R) +
                (if Self::segment_product(nums, i, R) < k { 1int } else { 0int }),
        decreases R - j,
    {
        if j == R {
            assert(Self::num_ends_upto(nums, k, i, R, R) == 0int);
            if Self::segment_product(nums, i, R) < k {
                assert(Self::num_ends_upto(nums, k, i, R + 1, R + 1) == 0int);
            }
        } else if Self::segment_product(nums, i, j) >= k {
            Self::lemma_segment_product_positive(nums, i, j, n);
            Self::lemma_product_ge_chain(nums, i, j, R, n);
        } else {
            Self::lemma_num_ends_upto_step(nums, k, i, j + 1, R, n);
        }
    }

    proof fn lemma_count_upto_step(
        nums: Seq<i32>, k: int, start: int, n: int, R: int, left: int,
    )
        requires
            0 <= start, 0 <= R < n, n <= nums.len(), 0 <= left <= R + 1,
            forall|x: int| 0 <= x < n ==> 1 <= #[trigger] nums[x] <= 1000,
            left <= R ==> Self::segment_product(nums, left, R) < k,
            forall|i: int| 0 <= i < left ==>
                #[trigger] Self::segment_product(nums, i, R) >= k,
        ensures
            Self::count_upto(nums, k, start, n, R + 1) ==
                Self::count_upto(nums, k, start, n, R) +
                (if left > R || start > R { 0int }
                 else if start >= left { R + 1 - start }
                 else { R + 1 - left }),
        decreases n - start,
    {
        if start >= n {
        } else {
            Self::lemma_count_upto_step(nums, k, start + 1, n, R, left);
            if start <= R {
                Self::lemma_num_ends_upto_step(nums, k, start, start, R, n);
                if start >= left && left <= R {
                    Self::lemma_product_mono_start(nums, left, start, R, n);
                }
            }
        }
    }

    #[verifier::loop_isolation(false)]
    pub fn num_subarray_product_less_than_k(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 30_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
            0 <= k <= 1_000_000,
        ensures
            res >= 0,
            res as int == Self::count_product_less(nums@, k as int, 0, nums.len() as int),
    {
        broadcast use vstd::std_specs::vec::axiom_spec_len;

        if k <= 1 {
            proof {
                Self::lemma_k_le_1_count_zero(
                    nums@, k as int, 0, nums@.len() as int);
            }
            return 0;
        }

        let n = nums.len();
        let ghost gn = n as int;
        let mut count: i32 = 0;
        let mut prod: u64 = 1;
        let mut left: usize = 0;
        let mut right: usize = 0;

        proof { Self::lemma_count_upto_zero(nums@, k as int, 0, gn); }

        while right < n
            invariant
                0 <= left <= right <= n,
                n == nums@.len(),
                gn == n as int,
                1 <= n <= 30_000,
                2 <= k <= 1_000_000,
                forall|i: int| 0 <= i < gn ==> 1 <= #[trigger] nums@[i] <= 1000,
                count >= 0,
                count as int == Self::count_upto(nums@, k as int, 0, gn, right as int),
                count as int <= (right as int) * gn,
                prod as int == Self::segment_product(
                    nums@, left as int, (right as int) - 1),
                left < right ==> (prod as u64) < (k as u64),
                forall|i: int| 0 <= i < left as int ==>
                    #[trigger] Self::segment_product(
                        nums@, i, (right as int) - 1) >= k as int,
            decreases n - right,
        {
            proof {
                Self::lemma_segment_product_positive(
                    nums@, left as int, (right as int) - 1, gn);
                assert(prod as int >= 1);
                assert(1 <= nums@[right as int] <= 1000);
                assert(prod as int <= 999_999) by {
                    if left < right {
                    } else {
                        assert(prod as int == 1);
                    }
                };
                assert((prod as int) * (nums@[right as int] as int)
                    <= 999_999_000int)
                    by(nonlinear_arith)
                    requires
                        (prod as int) <= 999_999,
                        1 <= (nums@[right as int] as int) <= 1000;
            }

            prod = prod * (nums[right] as u64);

            proof {
                if left as int == right as int {
                    assert(prod as int == nums@[right as int] as int);
                } else {
                    Self::lemma_segment_product_append(
                        nums@, left as int, right as int, gn);
                }

                assert forall|i: int| 0 <= i < left as int
                    implies #[trigger] Self::segment_product(
                        nums@, i, right as int) >= k as int
                by {
                    if right > 0 {
                        Self::lemma_product_ge_chain(
                            nums@, i, (right as int) - 1, right as int, gn);
                    }
                };
            }

            while left <= right && prod >= k as u64
                invariant
                    0 <= left <= right + 1,
                    right < n,
                    prod as int == Self::segment_product(
                        nums@, left as int, right as int),
                    forall|i: int| 0 <= i < left as int ==>
                        #[trigger] Self::segment_product(
                            nums@, i, right as int) >= k as int,
                decreases right + 1 - left,
            {
                let ghost sp_rest: int = Self::segment_product(
                    nums@, (left + 1) as int, right as int);
                let ghost divisor: int = nums@[left as int] as int;
                proof {
                    Self::lemma_segment_product_positive(
                        nums@, (left + 1) as int, right as int, gn);
                    assert(sp_rest >= 1);
                    assert(divisor >= 1);
                    if left == right {
                        assert(Self::segment_product(
                            nums@, left as int, right as int)
                            == nums@[left as int] as int);
                        assert(sp_rest == 1int);
                        assert(divisor * 1int == divisor)
                            by(nonlinear_arith)
                            requires divisor >= 1;
                    }
                    assert(prod as int == divisor * sp_rest);
                }
                prod = prod / (nums[left] as u64);
                proof {
                    assert(divisor * sp_rest / divisor == sp_rest)
                        by(nonlinear_arith)
                        requires divisor >= 1, sp_rest >= 0;
                    assert(prod as int == sp_rest);
                }
                left = left + 1;
            }

            proof {
                Self::lemma_count_upto_step(
                    nums@, k as int, 0, gn, right as int, left as int);
                Self::lemma_count_upto_nonneg(
                    nums@, k as int, 0, gn, (right + 1) as int);

                let delta = (right + 1 - left) as int;
                assert(0 <= delta <= (right as int) + 1);
                assert(count as int + delta
                    <= ((right as int) + 1) * gn)
                    by(nonlinear_arith)
                    requires
                        count as int <= (right as int) * gn,
                        0 <= delta,
                        delta <= (right as int) + 1,
                        gn >= 1,
                        (right as int) + 1 <= gn;
                assert(((right as int) + 1) * gn < 2_000_000_000int)
                    by(nonlinear_arith)
                    requires (right as int) < gn, gn <= 30_000;
            }

            count = count + ((right + 1 - left) as i32);
            right = right + 1;
        }

        proof { Self::lemma_count_upto_eq(nums@, k as int, 0, gn); }

        count
    }
}

}
