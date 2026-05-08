use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_contains(nums: Seq<i32>, k: i32) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] == k
    }

    pub open spec fn is_disappeared(nums: Seq<i32>, k: i32) -> bool {
        1 <= k <= nums.len() && !Self::seq_contains(nums, k)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn find_disappeared_numbers(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000, 
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
        ensures
            forall|i: int| 0 <= i < result.len() ==> #[trigger] Self::is_disappeared(nums@, result[i]),
            forall|k: int| 1 <= k <= nums.len() && Self::is_disappeared(nums@, k as i32) ==> #[trigger] Self::seq_contains(result@, k as i32),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] < #[trigger] result[j],
    {
        let n = nums.len();
        
        let mut seen: Vec<bool> = Vec::new();
        let mut idx: usize = 0;
        
        while idx < n + 1
            invariant
                n == nums.len(),
                n <= i32::MAX as usize,
                0 <= idx <= n + 1,
                seen.len() == idx,
                forall |k: int| 0 <= k < idx ==> #[trigger] seen[k] == false,
            decreases n + 1 - idx
        {
            seen.push(false);
            idx += 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                n <= i32::MAX as usize,
                seen.len() == n + 1,
                0 <= i <= n,
                forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= n,
                forall |k: int| 1 <= k <= n ==> (
                    #[trigger] seen[k] == true <==> exists|idx: int| 0 <= idx < i && nums[idx] == k
                ),
            decreases n - i
        {
            let val = nums[i] as usize;
            
            proof {
                assert(1 <= val <= n);
            }
            let ghost old_seen = seen@;
            
            seen.set(val, true);
            
            proof {
                assert forall |k: int| 1 <= k <= n implies (
                    #[trigger] seen[k] == true <==> exists|idx: int| 0 <= idx < i + 1 && nums[idx] == k
                ) by {
                    if k == val {
                        assert(seen[k] == true);
                        assert(0 <= (i as int) < (i + 1) as int && nums[i as int] == k);
                    } else {
                        assert(seen[k] == old_seen[k]);
                        if seen[k] == true {
                            let old_idx = choose|idx: int| 0 <= idx < i && nums[idx] == k;
                            assert(0 <= old_idx < (i + 1) as int && nums[old_idx] == k);
                        } else {
                            if exists|idx: int| 0 <= idx < i + 1 && nums[idx] == k {
                                let new_idx = choose|idx: int| 0 <= idx < i + 1 && nums[idx] == k;
                                if new_idx == i as int {
                                    assert(nums[new_idx] == nums[i as int] == val);
                                    assert(k == val);
                                } else {
                                    assert(0 <= new_idx < i as int && nums[new_idx] == k);
                                }
                            }
                        }
                    }
                }
            }
            i += 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 1;

        while k <= n
            invariant
                n == nums.len(),
                n <= i32::MAX as usize,
                seen.len() == n + 1,
                1 <= k <= n + 1,
                forall |val: int| 1 <= val <= n ==> (
                    #[trigger] seen[val] == true <==> exists|idx: int| 0 <= idx < n && nums[idx] == val
                ),
                forall|j: int| 0 <= j < result.len() ==> (
                    1 <= #[trigger] result[j] < k
                    && Self::is_disappeared(nums@, result[j])
                ),
                forall|m: int| 1 <= m < k && Self::is_disappeared(nums@, m as i32) ==>
                    #[trigger] Self::seq_contains(result@, m as i32),
                forall|i: int, j: int| 0 <= i < j < result.len() ==>
                    #[trigger] result[i] < #[trigger] result[j],
            decreases n + 1 - k
        {
            if !seen[k] {
                let ghost old_len = result.len();
                let ghost old_result = result@;
                
                result.push(k as i32);
                
                proof {
                    assert(!Self::seq_contains(nums@, k as i32));
                    assert(Self::is_disappeared(nums@, k as i32));
                    
                    assert forall|j: int| 0 <= j < result.len() implies (
                        1 <= #[trigger] result[j] <= k
                        && Self::is_disappeared(nums@, result[j])
                    ) by {
                        if j < old_len as int {
                            assert(result[j] == old_result[j]);
                            assert(result[j] < k as i32);
                        }
                    }
                    
                    assert forall|m: int| 1 <= m <= k && Self::is_disappeared(nums@, m as i32) implies
                        #[trigger] Self::seq_contains(result@, m as i32) by {
                        if m < k as int {
                            assert(Self::seq_contains(old_result, m as i32));
                            let wit = choose|idx: int| 0 <= idx < old_result.len() && old_result[idx] == m as i32;
                            assert(result@[wit] == m as i32);
                        } else {
                            assert(result[old_len as int] == m as i32);
                        }
                    }
                    
                    assert forall|i: int, j: int| 0 <= i < j < result.len() implies
                        #[trigger] result[i] < #[trigger] result[j] by {
                        if j < old_len as int {
                        } else {
                            assert(result[j] == k as i32);
                            assert(result[i] < k as i32);
                        }
                    }
                }
            } else {
                proof {
                    assert(Self::seq_contains(nums@, k as i32));
                    assert(!Self::is_disappeared(nums@, k as i32));
                    
                    assert forall|m: int| 1 <= m <= k && Self::is_disappeared(nums@, m as i32) implies
                        #[trigger] Self::seq_contains(result@, m as i32) by {
                        if m == k as int {
                        }
                    }
                    
                    assert forall|j: int| 0 <= j < result.len() implies (
                        1 <= #[trigger] result[j] <= k
                        && Self::is_disappeared(nums@, result[j])
                    ) by {
                        assert(result[j] < k as i32);
                    }
                }
            }
            k += 1;
        }

        result
    }
}

} 
