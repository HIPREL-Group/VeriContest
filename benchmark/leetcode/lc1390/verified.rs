use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn div_count_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { 1 + Self::div_count_from(n, d + 1) }
        else { Self::div_count_from(n, d + 1) }
    }

    pub open spec fn div_sum_from(n: int, d: int) -> int
        decreases n - d + 1
    {
        if d <= 0 || d > n { 0 }
        else if n % d == 0 { d + Self::div_sum_from(n, d + 1) }
        else { Self::div_sum_from(n, d + 1) }
    }

    pub open spec fn four_div_sum(nums: Seq<i32>, i: int) -> int
        decreases nums.len() - i
    {
        if i < 0 || i >= nums.len() { 0 }
        else if Self::div_count_from(nums[i] as int, 1) == 4 {
            Self::div_sum_from(nums[i] as int, 1) + Self::four_div_sum(nums, i + 1)
        }
        else { Self::four_div_sum(nums, i + 1) }
    }

    
    pub open spec fn div_count_range(n: int, lo: int, hi: int) -> int
        decreases (if lo >= 1 && lo <= hi { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi || lo <= 0 || lo > n { 0 }
        else if n % lo == 0 { 1 + Self::div_count_range(n, lo + 1, hi) }
        else { Self::div_count_range(n, lo + 1, hi) }
    }

    pub open spec fn div_sum_range(n: int, lo: int, hi: int) -> int
        decreases (if lo >= 1 && lo <= hi { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi || lo <= 0 || lo > n { 0 }
        else if n % lo == 0 { lo + Self::div_sum_range(n, lo + 1, hi) }
        else { Self::div_sum_range(n, lo + 1, hi) }
    }

    proof fn div_count_from_nonneg(n: int, d: int)
        ensures Self::div_count_from(n, d) >= 0
        decreases n - d + 1
    {
        if d <= 0 || d > n {} else {
            Self::div_count_from_nonneg(n, d + 1);
        }
    }

    proof fn div_sum_from_nonneg(n: int, d: int)
        requires n >= 1, d >= 1
        ensures Self::div_sum_from(n, d) >= 0
        decreases n - d + 1
    {
        if d > n {} else {
            Self::div_sum_from_nonneg(n, d + 1);
        }
    }

    proof fn div_count_range_nonneg(n: int, lo: int, hi: int)
        ensures Self::div_count_range(n, lo, hi) >= 0
        decreases (if lo >= 1 && lo <= hi { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi || lo <= 0 || lo > n {} else {
            Self::div_count_range_nonneg(n, lo + 1, hi);
        }
    }

    proof fn div_sum_range_nonneg(n: int, lo: int, hi: int)
        requires n >= 1, lo >= 1
        ensures Self::div_sum_range(n, lo, hi) >= 0
        decreases (if lo >= 1 && lo <= hi { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi || lo > n {} else {
            Self::div_sum_range_nonneg(n, lo + 1, hi);
        }
    }

    proof fn four_div_sum_nonneg(nums: Seq<i32>, i: int)
        requires forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000
        ensures Self::four_div_sum(nums, i) >= 0
        decreases nums.len() - i
    {
        if i < 0 || i >= nums.len() {
        } else if Self::div_count_from(nums[i] as int, 1) == 4 {
            Self::div_sum_from_nonneg(nums[i] as int, 1);
            Self::four_div_sum_nonneg(nums, i + 1);
        } else {
            Self::four_div_sum_nonneg(nums, i + 1);
        }
    }

    
    proof fn lemma_count_from_eq_range(n: int, d: int)
        requires n >= 1, d >= 1
        ensures Self::div_count_from(n, d) == Self::div_count_range(n, d, n)
        decreases n - d + 1
    {
        if d > n {
        } else {
            Self::lemma_count_from_eq_range(n, d + 1);
        }
    }

    proof fn lemma_sum_from_eq_range(n: int, d: int)
        requires n >= 1, d >= 1
        ensures Self::div_sum_from(n, d) == Self::div_sum_range(n, d, n)
        decreases n - d + 1
    {
        if d > n {
        } else {
            Self::lemma_sum_from_eq_range(n, d + 1);
        }
    }

    
    proof fn lemma_count_range_split(n: int, lo: int, mid: int, hi: int)
        requires n >= 1, lo >= 1, lo <= mid + 1, mid <= hi
        ensures Self::div_count_range(n, lo, hi) == Self::div_count_range(n, lo, mid) + Self::div_count_range(n, mid + 1, hi)
        decreases (if lo <= mid { mid - lo + 1 } else { 0 }) as nat
    {
        if lo > mid {
        } else if lo > n {
            Self::div_count_range_nonneg(n, mid + 1, hi);
        } else {
            Self::lemma_count_range_split(n, lo + 1, mid, hi);
        }
    }

    proof fn lemma_sum_range_split(n: int, lo: int, mid: int, hi: int)
        requires n >= 1, lo >= 1, lo <= mid + 1, mid <= hi
        ensures Self::div_sum_range(n, lo, hi) == Self::div_sum_range(n, lo, mid) + Self::div_sum_range(n, mid + 1, hi)
        decreases (if lo <= mid { mid - lo + 1 } else { 0 }) as nat
    {
        if lo > mid {
        } else if lo > n {
            Self::div_sum_range_nonneg(n, mid + 1, hi);
        } else {
            Self::lemma_sum_range_split(n, lo + 1, mid, hi);
        }
    }


    proof fn lemma_quotient_not_divisor(n: int, d: int)
        requires n >= 1, d >= 1, d * d <= n, n % d != 0,
        ensures n % (n / d) != 0
    {
        let q = n / d;
        let r = n % d;
        assert(q >= d) by (nonlinear_arith) requires d * d <= n, d >= 1, q == n / d;
        assert(r > 0);
        assert(r < d);
        assert(n == d * q + r) by (nonlinear_arith) requires q == n / d, r == n % d, d >= 1, n >= 1;
        if n % q == 0 {
            let k = n / q;
            assert(n == q * k) by (nonlinear_arith) requires n % q == 0, q >= 1, k == n / q;
            assert(q * (k - d) == r) by (nonlinear_arith) requires q * k == d * q + r;
            if k <= d {
                if k == d {
                    assert(r == 0) by (nonlinear_arith) requires q * (k - d) == r, k == d;
                } else {
                    assert(q * (k - d) <= 0) by (nonlinear_arith) requires k < d, q >= 1;
                }
                assert(false);
            } else {
                assert(k - d >= 1);
                assert(q * (k - d) >= q) by (nonlinear_arith) requires k - d >= 1, q >= 1;
                assert(r >= d);
                assert(false);
            }
        }
    }

    
    
    proof fn lemma_gap_count_zero(n: int, d: int)
        requires
            n >= 1, d >= 1, d * d <= n,
            n % d != 0,
        ensures
            Self::div_count_range(n, n / (d + 1) + 1, n / d) == 0,
            Self::div_sum_range(n, n / (d + 1) + 1, n / d) == 0,
        decreases n / d - n / (d + 1)
    {
        let lo = n / (d + 1) + 1;
        let hi = n / d;
        if lo > hi || lo <= 0 || lo > n {
        } else {
            Self::lemma_quotient_not_divisor(n, d);
            assert(n % hi != 0);
            assert(hi <= n) by (nonlinear_arith) requires hi == n / d, d >= 1, n >= 1;
            assert(Self::div_count_range(n, hi + 1, hi) == 0);
            assert(Self::div_count_range(n, hi, hi) == Self::div_count_range(n, hi + 1, hi));
            assert(Self::div_sum_range(n, hi + 1, hi) == 0);
            assert(Self::div_sum_range(n, hi, hi) == Self::div_sum_range(n, hi + 1, hi));
            if lo < hi {
                Self::lemma_gap_interior_zero(n, d, lo, hi - 1);
                Self::lemma_count_range_split(n, lo, hi - 1, hi);
                Self::lemma_sum_range_split(n, lo, hi - 1, hi);
            }
        }
    }

    
    proof fn lemma_gap_count_one(n: int, d: int)
        requires
            n >= 1, d >= 1, d * d <= n,
            n % d == 0, n / d != d,
        ensures
            Self::div_count_range(n, n / (d + 1) + 1, n / d) == 1,
            Self::div_sum_range(n, n / (d + 1) + 1, n / d) == n / d,
    {
        let q = n / d;
        let lo = n / (d + 1) + 1;
        assert(q >= 1) by (nonlinear_arith)
            requires d * d <= n, d >= 1, q == n / d;
        assert(q >= lo) by (nonlinear_arith)
            requires n >= 1, d >= 1, n % d == 0, n / d != d, q == n / d, lo == n / (d + 1) + 1, d * d <= n;
        assert(n == d * q) by (nonlinear_arith)
            requires n % d == 0, d >= 1, n >= 1, q == n / d;
        assert(n % q == 0) by (nonlinear_arith)
            requires n == d * q, d >= 1, q >= 1;
        assert(q <= n) by (nonlinear_arith)
            requires q == n / d, d >= 1, n >= 1;
        assert(Self::div_count_range(n, q + 1, q) == 0);
        assert(Self::div_count_range(n, q, q) == 1 + Self::div_count_range(n, q + 1, q));
        assert(Self::div_sum_range(n, q + 1, q) == 0);
        assert(Self::div_sum_range(n, q, q) == q + Self::div_sum_range(n, q + 1, q));
        if lo == q {
        } else {
            Self::lemma_count_range_split(n, lo, q - 1, q);
            Self::lemma_sum_range_split(n, lo, q - 1, q);
            Self::lemma_gap_interior_zero(n, d, lo, q - 1);
        }
    }

    
    proof fn lemma_gap_interior_zero(n: int, d: int, lo: int, hi: int)
        requires
            n >= 1, d >= 1, d * d <= n,
            lo >= n / (d + 1) + 1,
            hi < n / d,
            lo >= 1,
        ensures
            Self::div_count_range(n, lo, hi) == 0,
            Self::div_sum_range(n, lo, hi) == 0,
        decreases (if lo <= hi { hi - lo + 1 } else { 0 }) as nat
    {
        if lo > hi || lo > n {
        } else {
            
            
            
            
            assert((d + 1) * lo > n) by (nonlinear_arith)
                requires d >= 1, lo >= n / (d + 1) + 1, n >= 1;
            assert(d * lo < n) by (nonlinear_arith)
                requires d >= 1, hi < n / d, lo <= hi, n >= 1, lo >= 1;
            if n % lo == 0 {
                assert(n / lo > d) by (nonlinear_arith)
                    requires d * lo < n, d >= 1, lo >= 1, n % lo == 0;
                assert(n / lo <= d) by (nonlinear_arith)
                    requires (d + 1) * lo > n, lo >= 1, n % lo == 0;
                assert(false);
            }
            Self::lemma_gap_interior_zero(n, d, lo + 1, hi);
        }
    }

    
    proof fn lemma_perfect_sq_gap_empty(n: int, d: int)
        requires
            n >= 1, d >= 1, d * d == n, n % d == 0,
        ensures
            Self::div_count_range(n, d + 1, n / (d + 1)) == 0,
            Self::div_sum_range(n, d + 1, n / (d + 1)) == 0,
    {
        assert(n / (d + 1) == d - 1) by (nonlinear_arith)
            requires d * d == n, d >= 1;
        
    }

    pub fn sum_four_divisors(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            0 <= Self::four_div_sum(nums@, 0) <= i32::MAX as int,
        ensures
            result as int == Self::four_div_sum(nums@, 0),
    {
        let mut total: i32 = 0;
        let n = nums.len();
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                1 <= nums.len() <= 10_000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
                0 <= Self::four_div_sum(nums@, 0) <= i32::MAX as int,
                total as int + Self::four_div_sum(nums@, i as int) == Self::four_div_sum(nums@, 0),
                0 <= total as int,
            decreases n - i
        {
            let num = nums[i];
            let mut d: i32 = 1;
            let mut count: i32 = 0;
            let mut sum: i32 = 0;

            proof {
                Self::lemma_count_from_eq_range(num as int, 1);
                Self::lemma_sum_from_eq_range(num as int, 1);
            }

            while d * d <= num && count <= 4
                invariant
                    0 <= i < n,
                    n == nums.len(),
                    1 <= num <= 100_000,
                    num == nums[i as int],
                    1 <= d,
                    d as int <= num as int + 1,
                    d as int * d as int <= 100489,
                    0 <= count <= 6,
                    0 <= sum,
                    sum as int <= count as int * num as int,
                    count as int + Self::div_count_range(num as int, d as int, num as int / d as int) == Self::div_count_from(num as int, 1),
                    sum as int + Self::div_sum_range(num as int, d as int, num as int / d as int) == Self::div_sum_from(num as int, 1),
                decreases num as int - d as int + 1
            {
                let ghost nn = num as int;
                let ghost dd = d as int;
                let ghost qq = nn / dd;

                if num % d == 0 {
                    let ghost old_count = count as int;
                    let ghost old_sum = sum as int;

                    proof {
                        assert(dd <= qq) by (nonlinear_arith)
                            requires dd >= 1, dd * dd <= nn, qq == nn / dd;
                        assert(Self::div_count_range(nn, dd, qq) == 1 + Self::div_count_range(nn, dd + 1, qq));
                        assert(Self::div_sum_range(nn, dd, qq) == dd + Self::div_sum_range(nn, dd + 1, qq));
                        assert(dd <= nn) by (nonlinear_arith)
                            requires dd >= 1, dd * dd <= nn;
                    }

                    proof {
                        assert(dd <= nn) by (nonlinear_arith)
                            requires dd >= 1, dd * dd <= nn;
                        assert(old_count * nn + nn <= 500000) by (nonlinear_arith)
                            requires old_count <= 4, nn <= 100000, nn >= 1, old_count >= 0;
                        assert(old_sum + dd <= 500000) by (nonlinear_arith)
                            requires old_sum <= old_count * nn, dd <= nn, old_count * nn + nn <= 500000;
                    }

                    count = count + 1;
                    sum = sum + d;

                    let other: i32 = num / d;
                    if other != d {
                        proof {
                            let next_q = nn / (dd + 1);
                            assert(dd <= next_q) by (nonlinear_arith)
                                requires dd * dd <= nn, dd >= 1, nn >= 1,
                                         nn % dd == 0, nn / dd != dd, next_q == nn / (dd + 1);
                            assert(next_q <= qq) by (nonlinear_arith)
                                requires dd >= 1, next_q == nn / (dd + 1), qq == nn / dd, nn >= 1;
                            Self::lemma_count_range_split(nn, dd + 1, next_q, qq);
                            Self::lemma_sum_range_split(nn, dd + 1, next_q, qq);
                            Self::lemma_gap_count_one(nn, dd);
                            assert(Self::div_count_range(nn, next_q + 1, qq) == 1);
                            assert(Self::div_sum_range(nn, next_q + 1, qq) == qq);

                            assert(old_sum + dd + qq <= (old_count + 2) * nn) by (nonlinear_arith)
                                requires
                                    old_sum <= old_count * nn,
                                    dd <= nn,
                                    qq <= nn,
                                    dd >= 1,
                                    nn >= 1,
                                    0 <= old_count <= 4;
                        }

                        count = count + 1;
                        sum = sum + other;

                        proof {
                            let next_q = nn / (dd + 1);
                            assert(count as int + Self::div_count_range(nn, dd + 1, next_q) == Self::div_count_from(nn, 1));
                            assert(sum as int + Self::div_sum_range(nn, dd + 1, next_q) == Self::div_sum_from(nn, 1));
                        }
                    } else {
                        proof {
                            assert(dd * dd == nn) by (nonlinear_arith)
                                requires nn % dd == 0, nn / dd == dd, dd >= 1;
                            Self::lemma_perfect_sq_gap_empty(nn, dd);
                            let next_q = nn / (dd + 1);
                            assert(Self::div_count_range(nn, dd + 1, next_q) == 0);
                            assert(Self::div_sum_range(nn, dd + 1, next_q) == 0);

                            assert(sum as int <= count as int * nn) by (nonlinear_arith)
                                requires
                                    sum as int == old_sum + dd,
                                    count as int == old_count + 1,
                                    old_sum <= old_count * nn,
                                    dd <= nn,
                                    nn >= 1;
                        }
                    }
                } else {
                    
                    proof {
                        
                        assert(Self::div_count_range(nn, dd, qq) == Self::div_count_range(nn, dd + 1, qq));
                        assert(Self::div_sum_range(nn, dd, qq) == Self::div_sum_range(nn, dd + 1, qq));

                        let next_q = nn / (dd + 1);
                        if next_q < qq {
                            if dd <= next_q {
                                Self::lemma_count_range_split(nn, dd + 1, next_q, qq);
                                Self::lemma_sum_range_split(nn, dd + 1, next_q, qq);
                                Self::lemma_gap_count_zero(nn, dd);
                                assert(Self::div_count_range(nn, next_q + 1, qq) == 0);
                                assert(Self::div_sum_range(nn, next_q + 1, qq) == 0);
                            } else {
                                
                                
                                assert(qq == dd) by (nonlinear_arith)
                                    requires dd * dd <= nn, dd >= 1, nn >= 1,
                                             qq == nn / dd, dd > nn / (dd + 1);
                            }
                        } else {
                            
                            let ghost r_old: int = nn % dd;
                            let ghost r_new: int = nn % (dd + 1);
                            assert(nn == dd * qq + r_old) by (nonlinear_arith)
                                requires qq == nn / dd, r_old == nn % dd, dd >= 1;
                            assert(0 <= r_old && r_old < dd) by (nonlinear_arith)
                                requires r_old == nn % dd, dd >= 1;
                            assert(nn == (dd + 1) * next_q + r_new) by (nonlinear_arith)
                                requires next_q == nn / (dd + 1), r_new == nn % (dd + 1), dd >= 1;
                            assert(0 <= r_new && r_new < dd + 1) by (nonlinear_arith)
                                requires r_new == nn % (dd + 1), dd >= 1;
                            assert(next_q <= qq) by (nonlinear_arith)
                                requires dd >= 1, nn >= 1,
                                         nn == dd * qq + r_old,
                                         0 <= r_old, r_old < dd,
                                         nn == (dd + 1) * next_q + r_new,
                                         0 <= r_new, r_new < dd + 1;
                            assert(next_q == qq);
                        }
                        assert(count as int + Self::div_count_range(nn, dd + 1, next_q) == Self::div_count_from(nn, 1));
                        assert(sum as int + Self::div_sum_range(nn, dd + 1, next_q) == Self::div_sum_from(nn, 1));
                    }
                }

                proof {
                    assert(d as int <= num as int) by (nonlinear_arith)
                        requires d as int >= 1, d as int * d as int <= num as int;
                    assert(d as int <= 316) by (nonlinear_arith)
                        requires d as int * d as int <= num as int, num as int <= 100000, d as int >= 1;
                    assert((d as int + 1) * (d as int + 1) <= 100489) by (nonlinear_arith)
                        requires d as int >= 1, d as int <= 316;
                }
                d = d + 1;
            }

            proof {
                Self::div_count_range_nonneg(num as int, d as int, num as int / d as int);
                Self::div_sum_range_nonneg(num as int, d as int, num as int / d as int);
            }

            if count == 4 {
                proof {
                    
                    
                    
                    assert(d as int > num as int / d as int) by (nonlinear_arith)
                        requires d as int * d as int > num as int, d as int >= 1, num as int >= 1;
                    assert(Self::div_count_range(num as int, d as int, num as int / d as int) == 0);
                    assert(count as int == Self::div_count_from(num as int, 1));
                    assert(Self::div_sum_range(num as int, d as int, num as int / d as int) == 0);
                    assert(sum as int == Self::div_sum_from(num as int, 1));
                    assert(Self::four_div_sum(nums@, i as int) ==
                        Self::div_sum_from(nums[i as int] as int, 1) + Self::four_div_sum(nums@, (i + 1) as int));
                    Self::four_div_sum_nonneg(nums@, (i + 1) as int);
                }
                total = total + sum;
            } else {
                proof {
                    
                    if count > 4 {
                        
                        Self::div_count_range_nonneg(num as int, d as int, num as int / d as int);
                        assert(Self::div_count_from(num as int, 1) >= count as int);
                    } else {
                        
                        assert(d as int > num as int / d as int) by (nonlinear_arith)
                            requires d as int * d as int > num as int, d as int >= 1, num as int >= 1;
                        assert(Self::div_count_range(num as int, d as int, num as int / d as int) == 0);
                    }
                    assert(Self::div_count_from(num as int, 1) != 4);
                    assert(Self::four_div_sum(nums@, i as int) == Self::four_div_sum(nums@, (i + 1) as int));
                }
            }

            i = i + 1;
        }

        total
    }
}

}
