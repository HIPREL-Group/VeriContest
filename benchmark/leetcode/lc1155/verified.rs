use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    
    
    
    
    
    
    
    
    pub open spec fn ways(n: int, k: int, target: int) -> int
        decreases n,
    {
        if n <= 0 {
            if target == 0 { 1 } else { 0 }
        } else {
            Self::ways_sum(n, k, target, k)
        }
    }

    pub open spec fn ways_sum(n: int, k: int, target: int, f: int) -> int
        decreases n, f,
    {
        if n <= 0 || f <= 0 {
            0
        } else {
            Self::ways(n - 1, k, target - f) + Self::ways_sum(n, k, target, f - 1)
        }
    }

    proof fn lemma_ways_nonneg(n: int, k: int, target: int)
        requires
            k >= 1,
        ensures
            Self::ways(n, k, target) >= 0,
        decreases n, k + 1,
    {
        if n <= 0 {
        } else {
            Self::lemma_ways_sum_nonneg(n, k, target, k);
        }
    }

    proof fn lemma_ways_sum_nonneg(n: int, k: int, target: int, f: int)
        requires
            k >= 1,
            n >= 1,
        ensures
            Self::ways_sum(n, k, target, f) >= 0,
        decreases n, f,
    {
        if f <= 0 {
        } else {
            Self::lemma_ways_nonneg(n - 1, k, target - f);
            Self::lemma_ways_sum_nonneg(n, k, target, f - 1);
        }
    }

    proof fn lemma_ways_sum_step(n: int, k: int, target: int, f: int)
        requires
            n >= 1,
            k >= 1,
            f >= 1,
        ensures
            Self::ways_sum(n, k, target, f) == Self::ways(n - 1, k, target - f)
                + Self::ways_sum(n, k, target, f - 1),
    {
    }

    proof fn lemma_mod_add(a: int, b: int, m: int)
        requires
            m > 0,
            0 <= a,
            0 <= b,
        ensures
            (a % m + b % m) % m == (a + b) % m,
    {
        vstd::arithmetic::div_mod::lemma_add_mod_noop(a, b, m);
    }

    proof fn lemma_ways_zero_negative_target(n: int, k: int, target: int)
        requires
            k >= 1,
            n >= 0,
            target < 0,
        ensures
            Self::ways(n, k, target) == 0,
        decreases n, k + 1,
    {
        if n <= 0 {
        } else {
            Self::lemma_ways_sum_zero_negative_target(n, k, target, k);
        }
    }

    proof fn lemma_ways_sum_zero_negative_target(n: int, k: int, target: int, f: int)
        requires
            k >= 1,
            n >= 1,
            target < 0,
            1 <= f <= k,
        ensures
            Self::ways_sum(n, k, target, f) == 0,
        decreases n, f,
    {
        assert(target - f < 0);
        Self::lemma_ways_zero_negative_target(n - 1, k, target - f);
        assert(Self::ways(n - 1, k, target - f) == 0);
        if f > 1 {
            Self::lemma_ways_sum_zero_negative_target(n, k, target, f - 1);
            assert(Self::ways_sum(n, k, target, f - 1) == 0);
        } else {
            assert(f == 1);
            assert(Self::ways_sum(n, k, target, 0) == 0);
        }
    }

    proof fn lemma_ways_sum_zero_target(n: int, k: int, target: int, f: int)
        requires
            n >= 1,
            k >= 1,
            target <= 0,
            1 <= f <= k,
        ensures
            Self::ways_sum(n, k, target, f) == 0,
        decreases f,
    {
        assert(target - f < 0);
        Self::lemma_ways_zero_negative_target(n - 1, k, target - f);
        assert(Self::ways(n - 1, k, target - f) == 0);
        if f > 1 {
            Self::lemma_ways_sum_zero_target(n, k, target, f - 1);
            assert(Self::ways_sum(n, k, target, f - 1) == 0);
        } else {
            assert(f == 1);
            assert(Self::ways_sum(n, k, target, 0) == 0);
        }
    }

    
    
    proof fn lemma_ways_sum_slide(n: int, k: int, t: int, f: int)
        requires
            n >= 1,
            k >= 1,
            f >= 0,
        ensures
            Self::ways_sum(n, k, t, f) - Self::ways_sum(n, k, t - 1, f)
                == Self::ways(n - 1, k, t - 1) - Self::ways(n - 1, k, t - 1 - f),
        decreases f,
    {
        if f <= 0 {
        } else {
            Self::lemma_ways_sum_slide(n, k, t, f - 1);
        }
    }

    
    proof fn lemma_mod_sub(a: int, b: int, m: int)
        requires
            m > 0,
            a >= 0,
            b >= 0,
            a >= b,
        ensures
            (a % m - b % m + m) % m == (a - b) % m,
    {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a - b, m);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a % m - b % m + m, m);

        let ra = a % m;
        let rb = b % m;
        let rc = (a - b) % m;
        let x = ra - rb + m;
        let rx = x % m;
        let qa = a / m;
        let qb = b / m;
        let qc = (a - b) / m;
        let qx = x / m;

        
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(m, qc + qb - qa, 1 as int);
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(m, qc + qb, qa);
        vstd::arithmetic::mul::lemma_mul_is_distributive_add(m, qc, qb);
        let q1: int = qc + qb - qa + 1;
        assert(m * q1 == m * qc + m * qb - m * qa + m);
        assert(x == rc + m * q1);

        
        let delta: int = qx - q1;
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub(m, qx, q1);
        assert(m * delta == m * qx - m * q1);
        assert(rc - rx == m * delta);

        
        if delta >= 1 {
            vstd::arithmetic::mul::lemma_mul_inequality(1, delta, m);
            vstd::arithmetic::mul::lemma_mul_is_commutative(delta, m);
            assert(false);
        }
        if delta <= -1 {
            vstd::arithmetic::mul::lemma_mul_inequality(1, -delta, m);
            vstd::arithmetic::mul::lemma_mul_is_commutative(-delta, m);
            vstd::arithmetic::mul::lemma_mul_is_distributive_sub(m, 0 as int, delta);
            assert(m * (-delta) >= m);
            assert(m * delta <= -m);
            assert(false);
        }
    }

    pub fn num_rolls_to_target(n: i32, k: i32, target: i32) -> (result: i32)
        requires
            1 <= n <= 30,
            1 <= k <= 30,
            1 <= target <= 1000,
        ensures
            0 <= result < Self::MOD,
            result as int == Self::ways(n as int, k as int, target as int) % (Self::MOD as int),
    {
        let t = target as usize;
        let mut prev: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= t
            invariant
                0 <= idx <= t + 1,
                t <= 1000,
                prev@.len() == idx,
                forall|i: int| 0 <= i < idx as int ==> (#[trigger] prev@[i]) == 0i64,
            decreases t + 1 - idx,
        {
            prev.push(0i64);
            idx = idx + 1;
        }
        prev.set(0, 1i64);

        assert(prev@.len() == t + 1);
        assert(prev@[0] == 1i64);
        assert(forall|j: int| 1 <= j <= t as int ==> (#[trigger] prev@[j]) == 0i64);

        let mut die: i32 = 0;
        while die < n
            invariant
                0 <= die <= n,
                1 <= n <= 30,
                1 <= k <= 30,
                1 <= target <= 1000,
                t == target as usize,
                prev@.len() == t + 1,
                forall|j: int|
                    0 <= j <= t as int ==> 0 <= (#[trigger] prev@[j]) < Self::MOD,
                forall|j: int|
                    0 <= j <= t as int ==> (#[trigger] prev@[j]) as int
                        == Self::ways(die as int, k as int, j) % (Self::MOD as int),
            decreases n - die,
        {
            let mut curr: Vec<i64> = Vec::new();
            let mut idx2: usize = 0;
            while idx2 <= t
                invariant
                    0 <= idx2 <= t + 1,
                    t <= 1000,
                    curr@.len() == idx2,
                    forall|i: int| 0 <= i < idx2 as int ==> (#[trigger] curr@[i]) == 0i64,
                decreases t + 1 - idx2,
            {
                curr.push(0i64);
                idx2 = idx2 + 1;
            }

            let mut running_sum: i64 = 0;
            let mut j: usize = 1;

            proof {
                assert(curr@[0] == 0i64);
                Self::lemma_ways_sum_zero_target(die as int + 1, k as int, 0, k as int);
                assert(Self::ways_sum(die as int + 1, k as int, 0, k as int) == 0);
                assert(Self::ways(die as int + 1, k as int, 0) == Self::ways_sum(
                    die as int + 1,
                    k as int,
                    0,
                    k as int,
                ));
                assert(Self::ways(die as int + 1, k as int, 0) == 0);
                assert(curr@[0] as int == Self::ways(die as int + 1, k as int, 0) % (Self::MOD as int));
                assert(running_sum as int == Self::ways_sum(die as int + 1, k as int, 0, k as int) % (Self::MOD as int));
            }

            while j <= t
                invariant
                    1 <= j <= t + 1,
                    0 <= die < n,
                    1 <= n <= 30,
                    1 <= k <= 30,
                    1 <= target <= 1000,
                    t == target as usize,
                    curr@.len() == t + 1,
                    prev@.len() == t + 1,
                    forall|jj: int|
                        0 <= jj <= t as int ==> 0 <= (#[trigger] prev@[jj]) < Self::MOD,
                    forall|jj: int|
                        0 <= jj <= t as int ==> (#[trigger] prev@[jj]) as int
                            == Self::ways(die as int, k as int, jj) % (Self::MOD as int),
                    forall|jj: int|
                        0 <= jj < j as int ==> 0 <= (#[trigger] curr@[jj]) < Self::MOD,
                    forall|jj: int|
                        0 <= jj < j as int ==> (#[trigger] curr@[jj]) as int
                            == Self::ways(die as int + 1, k as int, jj) % (Self::MOD as int),
                    forall|jj: int|
                        j as int <= jj <= t as int ==> (#[trigger] curr@[jj]) == 0i64,
                    0 <= running_sum < Self::MOD,
                    running_sum as int == Self::ways_sum(die as int + 1, k as int, j as int - 1, k as int) % (Self::MOD as int),
                decreases t + 1 - j,
            {
                let ghost sum_prev = Self::ways_sum(die as int + 1, k as int, j as int - 1, k as int);
                let ghost ways_add = Self::ways(die as int, k as int, j as int - 1);
                let ghost ways_sub = Self::ways(die as int, k as int, j as int - 1 - k as int);

                proof {
                    Self::lemma_ways_sum_slide(die as int + 1, k as int, j as int, k as int);
                    Self::lemma_ways_nonneg(die as int, k as int, j as int - 1);
                    Self::lemma_ways_sum_nonneg(die as int + 1, k as int, j as int - 1, k as int);
                    Self::lemma_ways_sum_nonneg(die as int + 1, k as int, j as int, k as int);
                    
                    
                    
                    assert(Self::ways_sum(die as int + 1, k as int, j as int, k as int)
                        == sum_prev + ways_add - ways_sub);
                }

                
                running_sum = (running_sum + prev[j - 1]) % Self::MOD;

                proof {
                    Self::lemma_mod_add(sum_prev, ways_add, Self::MOD as int);
                    assert(running_sum as int == (sum_prev + ways_add) % (Self::MOD as int));
                }

                
                if j > k as usize {
                    proof {
                        Self::lemma_ways_nonneg(die as int, k as int, j as int - 1 - k as int);
                        assert(sum_prev + ways_add >= ways_sub);
                        Self::lemma_mod_sub(sum_prev + ways_add, ways_sub, Self::MOD as int);
                    }

                    running_sum = (running_sum - prev[j - 1 - k as usize] + Self::MOD) % Self::MOD;
                } else {
                    proof {
                        Self::lemma_ways_zero_negative_target(die as int, k as int, j as int - 1 - k as int);
                        assert(ways_sub == 0);
                    }
                }

                proof {
                    assert(running_sum as int == Self::ways_sum(die as int + 1, k as int, j as int, k as int) % (Self::MOD as int));
                    assert(Self::ways(die as int + 1, k as int, j as int) == Self::ways_sum(
                        die as int + 1,
                        k as int,
                        j as int,
                        k as int,
                    ));
                }

                curr.set(j, running_sum);

                j = j + 1;
            }

            prev = curr;
            die = die + 1;
        }

        prev[t] as i32
    }
}

} 
