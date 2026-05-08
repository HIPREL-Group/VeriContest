use vstd::prelude::*;
use std::collections::HashSet;

fn main() {}

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

proof fn lemma_bound(ab: i32, old_mask: i32, bit: i32, old_max_xor: i32)
    requires 
        0 <= bit <= 30,
        old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
        (ab & old_mask) <= old_max_xor,
        old_max_xor == old_max_xor & old_mask,
    ensures
        (ab & (old_mask | (1i32 << bit as u32))) <= old_max_xor | (1i32 << bit as u32)
{
    assert((ab & (old_mask | (1i32 << bit as u32))) <= old_max_xor | (1i32 << bit as u32)) by(bit_vector)
        requires 
            0 <= bit <= 30,
            old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
            (ab & old_mask) <= old_max_xor,
            old_max_xor == old_max_xor & old_mask;
}

proof fn lemma_bound_strict(v: i32, old_mask: i32, bit: i32, old_max_xor: i32)
    requires 
        0 <= bit <= 30,
        old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
        old_max_xor == old_max_xor & old_mask,
        v == v & (old_mask | (1i32 << bit as u32)),
        (v & old_mask) <= old_max_xor,
        v < old_max_xor | (1i32 << bit as u32),
    ensures
        v <= old_max_xor
{
    assert(v <= old_max_xor) by(bit_vector)
        requires 
            0 <= bit <= 30,
            old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
            old_max_xor == old_max_xor & old_mask,
            v == v & (old_mask | (1i32 << bit as u32)),
            (v & old_mask) <= old_max_xor,
            v < old_max_xor | (1i32 << bit as u32);
}

proof fn xor_dist(a: i32, b: i32, mask: i32)
    ensures (a ^ b) & mask == (a & mask) ^ (b & mask)
{
    assert((a ^ b) & mask == (a & mask) ^ (b & mask)) by(bit_vector);
}

proof fn xor_self_is_zero(a: i32)
    ensures a ^ a == 0
{
    assert(a ^ a == 0) by(bit_vector);
}

proof fn lemma_xor_target(nj: i32, nk: i32, mask: i32, target: i32, xor_val: i32)
    requires
        xor_val == nk & mask,
        xor_val == (nj & mask) ^ target,
    ensures
        ((nj & mask) ^ (nk & mask)) == target
{
    assert(xor_val ^ (nj & mask) == target) by(bit_vector) 
        requires xor_val == (nj & mask) ^ target;
    assert((nk & mask) ^ (nj & mask) == target) by(bit_vector)
        requires xor_val == nk & mask, xor_val ^ (nj & mask) == target;
    assert(((nj & mask) ^ (nk & mask)) == target) by(bit_vector)
        requires (nk & mask) ^ (nj & mask) == target;
}

proof fn xor_val_prop(nj: i32, nk: i32, mask: i32, target: i32, xor_val: i32)
    requires
        (nj & mask) ^ (nk & mask) == target,
        xor_val == (nj & mask) ^ target,
    ensures
        xor_val == (nk & mask)
{
    assert(xor_val == (nj & mask) ^ target);
    assert(xor_val == (nj & mask) ^ ((nj & mask) ^ (nk & mask)));
    assert((nj & mask) ^ ((nj & mask) ^ (nk & mask)) == ((nj & mask) ^ (nj & mask)) ^ (nk & mask)) by(bit_vector);
    assert(((nj & mask) ^ (nj & mask)) == 0) by(bit_vector);
    assert(0 ^ (nk & mask) == (nk & mask)) by(bit_vector);
}

proof fn lemma_mask_inv(bit: i32, old_mask: i32)
    requires 
        0 <= bit <= 30,
        old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 }
    ensures
        old_mask | (1i32 << bit as u32) == if bit - 1 == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> bit as u32) << bit as u32 }
{
    assert(old_mask | (1i32 << bit as u32) == if bit - 1 == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> bit as u32) << bit as u32 }) by(bit_vector)
        requires 
            0 <= bit <= 30,
            old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 };
}

proof fn lemma_target_non_neg(max_xor: i32, bit: i32)
    requires 
        0 <= bit <= 30,
        max_xor >= 0
    ensures
        max_xor | (1i32 << bit as u32) >= 0
{
    assert(max_xor | (1i32 << bit as u32) >= 0) by(bit_vector)
        requires 
            0 <= bit <= 30,
            max_xor >= 0;
}

pub struct Solution;

impl Solution {
    pub fn find_maximum_xor(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 200_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= i32::MAX, 
        ensures 
            forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                ==> res >= (nums[i] ^ nums[j]),
            exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                && res == (nums[i] ^ nums[j]),
            res >= 0,
    {
        if nums.len() == 1 {
            proof {
                xor_self_is_zero(nums[0int]);
            }
            return 0;
        }

        let mut max_xor = 0;
        let mut bit = 30;
        let mut mask: i32 = 0;

        proof {
            assert(0 == 0 & 0i32) by(bit_vector);
            assert forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() implies ((nums[i] ^ nums[j]) & 0i32) <= 0i32 by {
                let ab = nums[i] ^ nums[j];
                assert((ab & 0i32) == 0i32) by(bit_vector);
            };
            assert(exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && ((nums[i] ^ nums[j]) & 0i32) == 0i32) by {
                let ab = nums[0int] ^ nums[0int];
                assert((ab & 0i32) == 0i32) by(bit_vector);
            };
        }

        while bit >= 0 
            invariant
                1 <= nums.len() <= 200_000, 
                forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= i32::MAX, 
                -1 <= bit <= 30,
                max_xor >= 0,
                mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
                max_xor == max_xor & mask,
                forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() 
                    ==> ((nums[i] ^ nums[j]) & mask) <= max_xor,
                exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                    && ((nums[i] ^ nums[j]) & mask) == max_xor,
            decreases bit as int + 1
        {
            let old_mask = mask;
            let old_max_xor = max_xor;
            mask = mask | (1i32 << bit as u32);
            let mut prefixes: std::collections::HashSet<i32> = std::collections::HashSet::new(); 
            
            for i in 0..nums.len() 
                invariant
                    1 <= nums.len() <= 200_000, 
                    mask == old_mask | (1i32 << bit as u32),
                    forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= i32::MAX,
                    forall |idx: int| 0 <= idx < i ==> prefixes@.contains(nums[idx] & mask),
                    forall |v: i32| prefixes@.contains(v) ==> exists |idx: int| 0 <= idx < i && v == (nums[idx] & mask),
            {
                let prefix = nums[i] & mask;
                prefixes.insert(prefix);
                proof {
                    assert forall |v: i32| prefixes@.contains(v) implies exists |idx: int| 0 <= idx < (i + 1) && v == (nums[idx] & mask) by {
                        if v == (nums[i as int] & mask) {
                            assert(v == (nums[i as int] & mask));
                        }
                    };
                }
            }

            let target = max_xor | (1i32 << bit as u32);
            let mut found = false;
            
            for j in 0..nums.len()
                invariant
                    1 <= nums.len() <= 200_000, 
                    mask == old_mask | (1i32 << bit as u32),
                    target == old_max_xor | (1i32 << bit as u32),
                    forall |idx: int| 0 <= idx < nums.len() ==> 0 <= #[trigger] nums[idx] <= i32::MAX,
                    forall |idx: int| 0 <= idx < nums.len() ==> prefixes@.contains(#[trigger](nums[idx] & mask)),
                    forall |v: i32| #[trigger] prefixes@.contains(v) ==> exists |idx: int| 0 <= idx < nums.len() && v == (nums[idx] & mask),
                    found ==> exists |a: int, b: int| 0 <= a < nums.len() && 0 <= b < nums.len() && ((nums[a] & mask) ^ (nums[b] & mask)) == target,
                    !found ==> forall |a: int, b: int| 0 <= a < j && 0 <= b < nums.len() ==> ((nums[a] & mask) ^ (nums[b] & mask)) != target,
            {
                let xor_val = (nums[j] & mask) ^ target;
                if !found && prefixes.contains(&xor_val) {
                    found = true;
                    proof {
                        assert(prefixes@.contains(xor_val));
                        let k = choose |k: int| 0 <= k < nums.len() && xor_val == (nums[k] & mask);
                        lemma_xor_target(nums[j as int], nums[k], mask, target, xor_val);
                    }
                } else if !found {
                    proof {
                        assert(!prefixes@.contains(xor_val));
                        assert forall |b: int| 0 <= b < nums.len() implies ((nums[j as int] & mask) ^ (nums[b] & mask)) != target by {
                            if ((nums[j as int] & mask) ^ (nums[b] & mask)) == target {
                                xor_val_prop(nums[j as int], nums[b], mask, target, xor_val);
                                assert(prefixes@.contains(nums[b] & mask)); 
                                assert(false);
                            }
                        };
                    }
                }
            }
            
            if found {
                max_xor = target;
                proof {
                    lemma_target_non_neg(old_max_xor, bit);
                    let pair = choose |a: int, b: int| 0 <= a < nums.len() && 0 <= b < nums.len() && ((nums[a] & mask) ^ (nums[b] & mask)) == target;
                    let a = pair.0;
                    let b = pair.1;
                    xor_dist(nums[a], nums[b], mask);
                    assert(((nums[a] ^ nums[b]) & mask) == max_xor);
                }
            } else {
                proof {
                    assert(!found);
                    assert(exists |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && ((nums[i] ^ nums[j]) & mask) == max_xor) by {
                        let pair = choose |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && ((nums[i] ^ nums[j]) & old_mask) == old_max_xor;
                        let i_old = pair.0;
                        let j_old = pair.1;
                        let ab = nums[i_old] ^ nums[j_old];
                        xor_dist(nums[i_old], nums[j_old], mask);
                        assert((ab & mask) != target);
                        assert(ab & mask == old_max_xor || ab & mask == old_max_xor | (1i32 << bit as u32)) by(bit_vector)
                            requires 
                                0 <= bit <= 30,
                                old_mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 },
                                mask == old_mask | (1i32 << bit as u32),
                                old_max_xor == old_max_xor & old_mask,
                                ab & old_mask == old_max_xor;
                        assert(ab & mask == old_max_xor);
                    };
                }
            }
            
            proof {
                assert forall |j: int, k: int| 0 <= j < nums.len() && 0 <= k < nums.len() 
                        implies ((nums[j] ^ nums[k]) & mask) <= max_xor by {
                        let ab = nums[j] ^ nums[k];
                        if found {
                            lemma_bound(ab, old_mask, bit, old_max_xor);
                            xor_dist(nums[j], nums[k], mask);
                        } else {
                            xor_dist(nums[j], nums[k], mask);
                            assert(((nums[j] ^ nums[k]) & mask) != target);
                            
                            lemma_bound(ab, old_mask, bit, old_max_xor);
                            let v = ab & mask;
                            assert(v & old_mask == ab & old_mask) by(bit_vector)
                                requires v == ab & mask, mask == old_mask | (1i32 << bit as u32);
                            assert(v <= target); 
                            if v == target {
                                assert(false);
                            }
                            assert(v < target);
                            assert(v == v & mask) by(bit_vector)
                                requires v == ab & mask, mask == old_mask | (1i32 << bit as u32);
                            
                            lemma_bound_strict(v, old_mask, bit, old_max_xor);
                            assert(v <= max_xor);
                        }
                };
                
                assert(max_xor == max_xor & mask) by(bit_vector)
                    requires 
                        max_xor == old_max_xor || max_xor == old_max_xor | (1i32 << bit as u32),
                        old_max_xor == old_max_xor & old_mask,
                        mask == old_mask | (1i32 << bit as u32);
                        
                lemma_mask_inv(bit, old_mask);
            }
            
            bit -= 1;
        }

        proof {
            assert(mask == 0x7FFF_FFFFi32) by(bit_vector)
                requires 
                    bit == -1,
                    mask == if bit == 30 { 0i32 } else { (0x7FFF_FFFFi32 >> (bit + 1) as u32) << (bit + 1) as u32 };
                    
            assert forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() implies ((nums[i] ^ nums[j]) & mask) == (nums[i] ^ nums[j]) by {
                let ni = nums[i];
                let nj = nums[j];
                assert(((ni ^ nj) & mask) == (ni ^ nj)) by(bit_vector) 
                    requires 0 <= ni <= i32::MAX, 0 <= nj <= i32::MAX, mask == 0x7FFF_FFFFi32;
            };
        }

        max_xor
    }
}
}
