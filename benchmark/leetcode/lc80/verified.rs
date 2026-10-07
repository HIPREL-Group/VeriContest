use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_to(s: Seq<i32>, v: i32, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else { (if s[end - 1] == v { 1int } else { 0int }) + Self::count_to(s, v, end - 1) }
    }

    pub open spec fn min_2(x: int) -> int {
        if x <= 2 { x } else { 2 }
    }

    proof fn count_to_same_on_prefix(s1: Seq<i32>, s2: Seq<i32>, v: i32, end: int)
        requires
            end >= 0,
            s1.len() >= end,
            s2.len() >= end,
            forall |k: int| 0 <= k < end ==> s1[k] == s2[k],
        ensures
            Self::count_to(s1, v, end) == Self::count_to(s2, v, end),
        decreases end,
    {
        if end > 0 {
            Self::count_to_same_on_prefix(s1, s2, v, end - 1);
        }
    }

    proof fn count_to_zero_if_all_ne(s: Seq<i32>, val: i32, end: int)
        requires
            end >= 0,
            s.len() >= end,
            forall |i: int| 0 <= i < end ==> s[i] != val,
        ensures
            Self::count_to(s, val, end) == 0,
        decreases end,
    {
        if end > 0 {
            Self::count_to_zero_if_all_ne(s, val, end - 1);
        }
    }

    proof fn count_to_le_end(s: Seq<i32>, v: i32, end: int)
        requires
            end >= 0,
            s.len() >= end,
        ensures
            Self::count_to(s, v, end) <= end,
        decreases end,
    {
        if end > 0 {
            Self::count_to_le_end(s, v, end - 1);
        }
    }

    
    proof fn sorted_count_2_last_2(s: Seq<i32>, val: i32, end: int)
        requires
            end >= 2,
            s.len() >= end,
            forall |i: int, j: int| 0 <= i <= j < end ==> s[i] <= s[j],
            Self::count_to(s, val, end) >= 2,
            s[end - 1] <= val,
        ensures
            s[end - 1] == val,
            s[end - 2] == val,
    {
        if s[end - 1] < val {
            assert forall |i: int| 0 <= i < end implies s[i] != val by {
                assert(s[i] <= s[end - 1]);
            };
            Self::count_to_zero_if_all_ne(s, val, end);
            assert(false);
        }
        
        
        if s[end - 2] < val {
            assert forall |i: int| 0 <= i < end - 1 implies s[i] != val by {
                assert(s[i] <= s[end - 2]);
            };
            Self::count_to_zero_if_all_ne(s, val, end - 1);
            assert(false);
        }
        
    }

    proof fn count_to_nonneg(s: Seq<i32>, val: i32, end: int)
        requires
            end >= 0,
            s.len() >= end,
        ensures
            Self::count_to(s, val, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::count_to_nonneg(s, val, end - 1);
        }
    }

    proof fn count_to_ge_1_from_elem(s: Seq<i32>, val: i32, end: int, pos: int)
        requires
            end >= 1,
            s.len() >= end,
            0 <= pos < end,
            s[pos] == val,
        ensures
            Self::count_to(s, val, end) >= 1,
        decreases end,
    {
        if pos == end - 1 {
            Self::count_to_nonneg(s, val, end - 1);
        } else {
            Self::count_to_ge_1_from_elem(s, val, end - 1, pos);
        }
    }

    
    proof fn count_to_ge_2_from_last_2(s: Seq<i32>, val: i32, end: int)
        requires
            end >= 2,
            s.len() >= end,
            s[end - 1] == val,
            s[end - 2] == val,
        ensures
            Self::count_to(s, val, end) >= 2,
    {
        
        Self::count_to_ge_1_from_elem(s, val, end - 1, end - 2);
    }

    pub fn remove_duplicates(nums: &mut Vec<i32>) -> (k: i32)
        requires
            1 <= old(nums).len() <= 30_000,
            forall |i: int| 0 <= i < old(nums).len() ==>
                -10_000 <= #[trigger] old(nums)[i] <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < old(nums).len() ==>
                old(nums)[i] <= old(nums)[j],
        ensures
            1 <= k <= nums.len(),
            nums.len() == old(nums).len(),
            forall |i: int, j: int| 0 <= i <= j < k as int ==>
                nums[i] <= nums[j],
            forall |i: int| 0 <= i < k as int - 2 ==>
                #[trigger] nums[i] < nums[i + 2],
            forall |v: i32|
                Self::count_to(nums@, v, k as int) ==
                    Self::min_2(Self::count_to(old(nums)@, v, old(nums).len() as int)),
    {
        let n = nums.len();
        let mut slow: usize = 0;
        let mut fast: usize = 0;

        while fast < n
            invariant
                n == nums.len(),
                nums.len() == old(nums).len(),
                1 <= n <= 30_000,
                0 <= slow <= fast <= n,
                fast >= 1 ==> slow >= 1,
                forall |i: int| 0 <= i < n as int ==>
                    -10_000 <= #[trigger] old(nums)[i] <= 10_000,
                forall |i: int, j: int| 0 <= i <= j < n as int ==>
                    old(nums)[i] <= old(nums)[j],
                forall |i: int| fast as int <= i < n as int ==>
                    nums[i] == old(nums)[i],
                forall |i: int, j: int| 0 <= i <= j < slow as int ==>
                    nums[i] <= nums[j],
                forall |i: int| 0 <= i < slow as int - 2 ==>
                    #[trigger] nums[i] < nums[i + 2],
                forall |i: int| 0 <= i < slow as int ==>
                    -10_000 <= #[trigger] nums[i] <= 10_000,
                slow >= 1 ==> nums[slow as int - 1] == old(nums)[fast as int - 1],
                forall |v: i32|
                    Self::count_to(nums@, v, slow as int) ==
                        Self::min_2(Self::count_to(old(nums)@, v, fast as int)),
            decreases n - fast,
        {
            let ghost pre = nums@;
            let ghost old_slow = slow as int;

            if slow < 2 || nums[fast] != nums[slow - 2] {
                let val = nums[fast];
                nums.set(slow, val);
                slow = slow + 1;

                proof {
                    assert(pre[fast as int] == old(nums)[fast as int]);
                    assert(val == old(nums)[fast as int]);
                    assert(nums@ =~= pre.update(old_slow, val));

                    
                    if old_slow >= 1 {
                        assert(pre[old_slow - 1] == old(nums)[fast as int - 1]);
                        assert(old(nums)[fast as int - 1] <= old(nums)[fast as int]);
                        assert(pre[old_slow - 1] <= val);
                    }

                    if old_slow >= 2 {
                        assert(pre[old_slow - 2] <= pre[old_slow - 1]);
                        assert(pre[old_slow - 2] != val);
                        assert(pre[old_slow - 2] < val);
                    }

                    assert forall |i: int, j: int| 0 <= i <= j < slow as int
                        implies nums[i] <= nums[j] by {
                        if j < old_slow {
                            assert(nums[i] == pre[i]);
                            assert(nums[j] == pre[j]);
                        } else if i < old_slow {
                            assert(nums[j] == val);
                            assert(nums[i] == pre[i]);
                            if old_slow >= 1 {
                                assert(pre[i] <= pre[old_slow - 1]);
                                assert(pre[old_slow - 1] <= val);
                            }
                        }
                    };

                    
                    assert forall |i: int| 0 <= i < slow as int - 2
                        implies #[trigger] nums[i] < nums[i + 2] by {
                        if i + 2 < old_slow {
                            assert(nums[i] == pre[i]);
                            assert(nums[i + 2] == pre[i + 2]);
                        } else if old_slow >= 2 {
                            assert(i == old_slow - 2);
                            assert(nums[i] == pre[old_slow - 2]);
                            assert(nums[i + 2] == val);
                        }
                    };

                    
                    assert forall |i: int| fast as int + 1 <= i < n as int
                        implies nums[i] == old(nums)[i] by {
                        assert(nums[i] == pre[i]);
                    };

                    
                    assert forall |vv: i32|
                        Self::count_to(nums@, vv, slow as int) ==
                        Self::min_2(Self::count_to(old(nums)@, vv, fast as int + 1)) by {
                        Self::count_to_same_on_prefix(nums@, pre, vv, old_slow);
                        
                        
                        
                        if vv == val {
                            
                            
                            if Self::count_to(old(nums)@, val, fast as int) >= 2 {
                                
                                
                                Self::count_to_le_end(pre, val, old_slow);
                                
                                
                                Self::sorted_count_2_last_2(pre, val, old_slow);
                                
                                
                                
                                
                                
                                assert(false);
                            }
                        }
                    };

                    assert(-10_000 <= val <= 10_000);
                    assert(nums[slow as int - 1] == val);
                }
            } else {
                proof {
                    assert(nums[fast as int] == old(nums)[fast as int]);
                    assert(pre[old_slow - 2] == old(nums)[fast as int]);
                    assert(pre[old_slow - 2] <= pre[old_slow - 1]);
                    assert(pre[old_slow - 1] == old(nums)[fast as int - 1]);
                    assert(old(nums)[fast as int - 1] <= old(nums)[fast as int]);
                    assert(nums[old_slow - 1] == old(nums)[fast as int]);

                    
                    let ghost val = old(nums)[fast as int];
                    assert forall |vv: i32|
                        Self::count_to(nums@, vv, slow as int) ==
                        Self::min_2(Self::count_to(old(nums)@, vv, fast as int + 1)) by {
                        
                        
                        if vv == val {
                            
                            
                            if Self::count_to(old(nums)@, val, fast as int) < 2 {
                                
                                
                                
                                
                                
                                
                                
                                assert(pre[old_slow - 1] == val);
                                assert(pre[old_slow - 2] == val);
                                Self::count_to_ge_2_from_last_2(pre, val, old_slow);
                                assert(false);
                            }
                        }
                    };
                }
            }
            fast = fast + 1;
        }

        slow as i32
    }
}

}
