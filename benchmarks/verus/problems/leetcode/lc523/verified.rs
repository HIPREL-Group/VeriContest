use vstd::prelude::*;
use std::collections::HashMap;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;
use vstd::arithmetic::div_mod::*;

pub struct Solution;

impl Solution {
    pub open spec fn get_sum(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start, 
    {
        if start >= end {
            0
        } else {
            nums[start] + Self::get_sum(nums, start + 1, end)
        }
    }

    proof fn lemma_get_sum_extend(nums: Seq<i32>, start: int, end: int)
        requires
            0 <= start < end,
            end <= nums.len(),
        ensures
            Self::get_sum(nums, start, end) == Self::get_sum(nums, start, end - 1) + nums[end - 1],
        decreases end - start,
    {
        if start + 1 == end {
            assert(Self::get_sum(nums, start, end - 1) == 0);
            assert(Self::get_sum(nums, start, end) == nums[start] + Self::get_sum(nums, start + 1, end));
            assert(Self::get_sum(nums, start + 1, end) == 0);
        } else {
            Self::lemma_get_sum_extend(nums, start + 1, end);
            assert(Self::get_sum(nums, start, end) == nums[start] + Self::get_sum(nums, start + 1, end));
            assert(Self::get_sum(nums, start, end - 1) == nums[start] + Self::get_sum(nums, start + 1, end - 1));
        }
    }

    proof fn lemma_get_sum_split(nums: Seq<i32>, a: int, b: int, c: int)
        requires 
            0 <= a <= b <= c <= nums.len()
        ensures
            Self::get_sum(nums, a, c) == Self::get_sum(nums, a, b) + Self::get_sum(nums, b, c)
        decreases b - a
    {
        if a == b {
        } else {
            Self::lemma_get_sum_split(nums, a + 1, b, c);
        }
    }

    proof fn lemma_mod_sub(a: int, b: int, k: int)
        requires 
            k > 0,
            a >= 0,
            b >= 0,
            a % k == b % k,
        ensures 
            (a - b) % k == 0int,
    {
        lemma_fundamental_div_mod(a, k);
        lemma_fundamental_div_mod(b, k);
        let q_a = a / k;
        let q_b = b / k;
        
        assert(a == k * q_a + (a % k));
        assert(b == k * q_b + (b % k));
        
        assert(a - b == k * (q_a - q_b)) by (nonlinear_arith)
            requires 
                a == k * q_a + a % k,
                b == k * q_b + b % k,
                a % k == b % k;
                
        lemma_mod_multiples_vanish(q_a - q_b, 0, k);
        assert(((q_a - q_b) * k + 0) % k == 0int % k);
        assert(k * (q_a - q_b) == (q_a - q_b) * k) by (nonlinear_arith);
        
        assert(0int % k == 0int) by {
            lemma_fundamental_div_mod(0int, k);
        };
    }

    proof fn lemma_mod_sub_converse(a: int, b: int, k: int)
        requires 
            k > 0,
            a >= 0,
            b >= 0,
            (a - b) % k == 0int,
        ensures 
            a % k == b % k,
    {
        lemma_fundamental_div_mod(a, k);
        lemma_fundamental_div_mod(b, k);
        lemma_fundamental_div_mod(a - b, k);
        let q_a = a / k;
        let q_b = b / k;
        let q_sub = (a - b) / k;
        
        assert(a == k * q_a + (a % k));
        assert(b == k * q_b + (b % k));
        assert(a - b == k * q_sub + ((a - b) % k));
        assert(a - b == k * q_sub + 0int);
        assert(a - b == k * q_sub);
        
        assert(a % k == b % k) by (nonlinear_arith)
            requires 
                a == k * q_a + a % k,
                b == k * q_b + b % k,
                a - b == k * q_sub;
    }

    pub fn check_subarray_sum(nums: Vec<i32>, k: i32) -> (res: bool) 
        requires
            1 <= nums.len() <= 100_000, 
            forall |i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 1_000_000_000, 
            forall |i: int, j: int| 0 <= i < j <= nums@.len() ==> 0 <= #[trigger] Self::get_sum(nums@, i, j) <= i32::MAX, 
            1 <= k <= i32::MAX, 
        ensures 
            res == (exists |i: int, j: int| 
                0 <= i < j <= nums@.len() && 
                j - i >= 2 &&
                Self::get_sum(nums@, i, j) % (k as int) == 0)
    {
        let mut map: HashMap<i32, usize> = HashMap::new();
        map.insert(0, 0);
        
        let mut sum: i64 = 0;
        let mut i: usize = 0;
        
        let ghost mut sums: Seq<int> = Seq::empty();
        proof {
            sums = sums.push(0);
            assert(Self::get_sum(nums@, 0, 0) == 0);
            lemma_fundamental_div_mod(0int, k as int);
            assert(0int % (k as int) == 0);
            assert(map@.contains_key(0i32));
            assert(map@[0i32] == 0);
            
            assert forall |v: i32| #[trigger] map@.contains_key(v) implies 
                0 <= map@[v] <= i && 
                v as int == Self::get_sum(nums@, 0, map@[v] as int) % (k as int) by {
                if v == 0 {
                } else {
                }
            }
            assert forall |x: int| 0 <= x <= i implies 
                map@.contains_key((#[trigger] Self::get_sum(nums@, 0, x) % (k as int)) as i32) by {
                if x == 0 {
                }
            }
        }

        while i < nums.len()
            invariant
                1 <= nums.len() <= 100_000, 
                forall |idx: int| 0 <= idx < nums@.len() ==> 0 <= #[trigger] nums@[idx] <= 1_000_000_000, 
                forall |a: int, b: int| 0 <= a <= b <= nums@.len() ==> 0 <= #[trigger] Self::get_sum(nums@, a, b) <= i32::MAX, 
                1 <= k <= i32::MAX, 
                0 <= i <= nums.len(),
                sum == Self::get_sum(nums@, 0, i as int),
                sums.len() == i as int + 1,
                forall |x: int| 0 <= x <= i ==> #[trigger] sums[x] == Self::get_sum(nums@, 0, x),
                forall |a: int, b: int| 
                    0 <= a < b <= i && b - a >= 2 ==>
                    Self::get_sum(nums@, a, b) % (k as int) != 0,
                forall |v: i32| #[trigger] map@.contains_key(v) ==> 
                    0 <= map@[v] <= i && 
                    v as int == Self::get_sum(nums@, 0, map@[v] as int) % (k as int),
                forall |x: int| 0 <= x <= i ==> 
                    map@.contains_key((#[trigger] Self::get_sum(nums@, 0, x) % (k as int)) as i32),
                forall |v: i32, x: int| (#[trigger] map@.contains_key(v) && 0 <= x <= i && 
                    (#[trigger] Self::get_sum(nums@, 0, x) % (k as int)) as i32 == v) ==> 
                    map@[v] as int <= x,
            decreases nums.len() - i, 
        {
            sum = sum + nums[i] as i64;
            
            proof {
                Self::lemma_get_sum_extend(nums@, 0, i as int + 1);
                sums = sums.push(sum as int);
            }
            
            let r = (sum % (k as i64)) as i32;
            
            if let Some(prev) = map.get(&r) {
                if i + 1 - *prev >= 2 {
                    proof {
                        let a = *prev as int;
                        let b = i as int + 1;
                        assert(map@[r] == *prev);
                        assert(0 <= a <= i as int);
                        assert(b - a >= 2);
                        
                        let sum_a = Self::get_sum(nums@, 0, a);
                        let sum_b = Self::get_sum(nums@, 0, b);
                        
                        assert(sum_a % (k as int) == r as int);
                        assert(sum_b % (k as int) == r as int);
                        
                        Self::lemma_mod_sub(sum_b, sum_a, k as int);
                        assert((sum_b - sum_a) % (k as int) == 0);
                        
                        Self::lemma_get_sum_split(nums@, 0, a, b);
                        assert(sum_b - sum_a == Self::get_sum(nums@, a, b));
                        assert(Self::get_sum(nums@, a, b) % (k as int) == 0);
                    }
                    return true;
                } else {
                    proof {
                        let b = i as int + 1;
                        assert(*prev as int == i as int);
                        
                        assert forall |a: int, b_prime: int| 
                            0 <= a < b_prime <= b && b_prime - a >= 2 
                            implies Self::get_sum(nums@, a, b_prime) % (k as int) != 0 by 
                        {
                            if b_prime == b {
                                if Self::get_sum(nums@, a, b_prime) % (k as int) == 0 {
                                    let sum_a = Self::get_sum(nums@, 0, a);
                                    let sum_b = Self::get_sum(nums@, 0, b);
                                    Self::lemma_get_sum_split(nums@, 0, a, b);
                                    assert(sum_b - sum_a == Self::get_sum(nums@, a, b));
                                    
                                    Self::lemma_mod_sub_converse(sum_b, sum_a, k as int);
                                    assert(sum_a % (k as int) == sum_b % (k as int));
                                    assert(sum_b % (k as int) == r as int);
                                    assert(sum_a % (k as int) == r as int);
                                    
                                    assert(map@.contains_key(r));
                                    assert(map@[r] as int <= a);
                                    assert(*prev as int <= a);
                                    assert(*prev as int <= b_prime - 2);
                                }
                            }
                        }
                    }
                }
            } else {
                map.insert(r, i + 1);
                proof {
                    let b = i as int + 1;
                    assert forall |a: int, b_prime: int| 
                        0 <= a < b_prime <= b && b_prime - a >= 2 
                        implies Self::get_sum(nums@, a, b_prime) % (k as int) != 0 by 
                    {
                        if b_prime == b {
                            if Self::get_sum(nums@, a, b_prime) % (k as int) == 0 {
                                let sum_a = Self::get_sum(nums@, 0, a);
                                let sum_b = Self::get_sum(nums@, 0, b);
                                Self::lemma_get_sum_split(nums@, 0, a, b);
                                assert(sum_b - sum_a == Self::get_sum(nums@, a, b_prime));
                                Self::lemma_mod_sub_converse(sum_b, sum_a, k as int);
                                assert(sum_a % (k as int) == sum_b % (k as int));
                                assert(sum_b % (k as int) == r as int);
                                assert(sum_a % (k as int) == r as int);
                                
                                let rem_a = (sum_a % (k as int)) as i32;
                                assert(map@.contains_key(rem_a));
                                assert(rem_a == r);
                                assert(map@.contains_key(r));
                            }
                        }
                    }
                }
            }
            
            i = i + 1;
        }
        
        false
    }
}

}