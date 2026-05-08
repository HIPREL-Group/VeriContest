use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    

    pub open spec fn contains_value(nums: Seq<i32>, v: int) -> bool {
        exists|i: int| 0 <= i < nums.len() && nums[i] as int == v
    }

    
    pub open spec fn count_correct(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_correct(nums, end - 1)
                + if nums[end - 1] as int == end { 1int } else { 0int }
        }
    }

    

    proof fn lemma_count_correct_nonneg(nums: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= nums.len(),
        ensures
            Self::count_correct(nums, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_correct_nonneg(nums, end - 1);
        }
    }

    proof fn lemma_count_correct_bounded(nums: Seq<i32>, end: int)
        requires
            end >= 0,
            end <= nums.len(),
        ensures
            Self::count_correct(nums, end) <= end,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_correct_bounded(nums, end - 1);
        }
    }

    
    proof fn lemma_update_count_correct(nums: Seq<i32>, pos: int, val: i32, end: int)
        requires
            0 <= pos < nums.len(),
            end >= 0,
            end <= nums.len(),
        ensures
            Self::count_correct(nums.update(pos, val), end)
                == Self::count_correct(nums, end)
                   - (if pos < end && nums[pos] as int == pos + 1 { 1int } else { 0int })
                   + (if pos < end && val as int == pos + 1 { 1int } else { 0int }),
        decreases end,
    {
        if end > 0 {
            Self::lemma_update_count_correct(nums, pos, val, end - 1);
        }
    }

    
    proof fn lemma_swap_preserves_contains(
        before: Seq<i32>, after: Seq<i32>, i: int, j: int, v: int,
    )
        requires
            before.len() == after.len(),
            0 <= i < before.len(),
            0 <= j < before.len(),
            after == before.update(j, before[i]).update(i, before[j]),
        ensures
            Self::contains_value(after, v) == Self::contains_value(before, v),
    {
        
        if Self::contains_value(before, v) {
            let wit = choose|k: int| 0 <= k < before.len() && before[k] as int == v;
            if wit == i {
                
                
                
                if i == j {
                    assert(after[i] as int == v);
                } else {
                    assert(after[j] == before[i]);
                    assert(after[j] as int == v);
                }
            } else if wit == j {
                
                assert(after[i] == before[j]);
                assert(after[i] as int == v);
            } else {
                
                assert(after[wit] == before[wit]);
                assert(after[wit] as int == v);
            }
        }
        
        if Self::contains_value(after, v) {
            let wit = choose|k: int| 0 <= k < after.len() && after[k] as int == v;
            if wit == i {
                
                assert(before[j] as int == v);
            } else if wit == j {
                if i == j {
                    assert(before[i] as int == v);
                } else {
                    
                    assert(after[j] == before[i]);
                    assert(before[i] as int == v);
                }
            } else {
                assert(after[wit] == before[wit]);
                assert(before[wit] as int == v);
            }
        }
    }

    

    pub fn first_missing_positive(nums: Vec<i32>) -> (result: i32)
        requires
            nums.len() >= 1,
            nums.len() <= 100_000,
        ensures
            result >= 1,
            !Self::contains_value(nums@, result as int),
            forall|v: int| 1 <= v < result as int ==> Self::contains_value(nums@, v),
    {
        let n = nums.len();
        let mut arr = nums;
        let n_i32 = n as i32;

        
        let mut i: usize = 0;
        while i < n
            invariant
                n == arr@.len(),
                n <= 100_000,
                n_i32 == n as i32,
                0 <= i <= n,
                
                forall|v: int|
                    Self::contains_value(arr@, v) == Self::contains_value(nums@, v),
                
                forall|k: int|
                    #![trigger arr@[k]]
                    0 <= k < i as int && 1 <= arr@[k] as int <= n as int
                    ==> arr@[(arr@[k] as int - 1)] == arr@[k],
            decreases n - i,
        {
            
            while arr[i] >= 1 && arr[i] <= n_i32
                && arr[(arr[i] as usize) - 1] != arr[i]
                invariant
                    n == arr@.len(),
                    n <= 100_000,
                    n_i32 == n as i32,
                    0 <= i < n,
                    
                    forall|v: int|
                        Self::contains_value(arr@, v) == Self::contains_value(nums@, v),
                    
                    forall|k: int|
                        #![trigger arr@[k]]
                        0 <= k < i as int && 1 <= arr@[k] as int <= n as int
                        ==> arr@[(arr@[k] as int - 1)] == arr@[k],
                decreases n as int - Self::count_correct(arr@, n as int),
            {
                let j = (arr[i] as usize) - 1;
                let vi = arr[i];
                let vj = arr[j];

                
                let ghost before = arr@;

                proof {
                    assert(before[j as int] as int != (j + 1) as int) by {
                    };

                    assert(i != j) by {
                    };
                    assert(before[i as int] as int != (i + 1) as int);
                }

                arr.set(j, vi);
                arr.set(i, vj);

                proof {
                    let after = arr@;

                    
                    assert forall|v: int| #![auto]
                        Self::contains_value(after, v) == Self::contains_value(nums@, v)
                    by {
                        Self::lemma_swap_preserves_contains(before, after, i as int, j as int, v);
                    };

                    
                    let mid = before.update(j as int, vi);
                    Self::lemma_update_count_correct(before, j as int, vi, n as int);
                    assert(Self::count_correct(mid, n as int)
                        == Self::count_correct(before, n as int) + 1);

                    Self::lemma_update_count_correct(mid, i as int, vj, n as int);
                    assert(mid[i as int] == before[i as int]);
                    assert(Self::count_correct(after, n as int)
                        >= Self::count_correct(before, n as int) + 1);

                    Self::lemma_count_correct_bounded(after, n as int);
                    Self::lemma_count_correct_nonneg(before, n as int);

                    
                    assert forall|k: int|
                        #![trigger arr@[k]]
                        0 <= k < i as int && 1 <= arr@[k] as int <= n as int
                        implies arr@[(arr@[k] as int - 1)] == arr@[k]
                    by {
                        if k == j as int {
                            assert(after[k] as int == (k + 1));
                            assert(after[(after[k] as int - 1)] == after[k]);
                        } else {
                            assert(after[k] == before[k]);

                            let t = before[k] as int - 1;
                            assert(before[t] == before[k]);

                            assert(t != j as int) by {
                                if t == j as int {
                                    assert(before[j as int] == before[k]);
                                    assert(before[k] as int == j as int + 1);
                                    assert(before[j as int] as int == j as int + 1);
                                    assert(before[i as int] as int == j as int + 1);
                                    assert(before[j as int] == before[i as int]);
                                    assert(false);
                                }
                            };

                            assert(t != i as int) by {
                                if t == i as int {
                                    assert(before[k] as int == i as int + 1);
                                    assert(before[i as int] == before[k]);
                                    assert(before[i as int] as int == i as int + 1);
                                    assert(false);
                                }
                            };

                            assert(after[t] == before[t]);
                            assert(after[t] == after[k]);
                        }
                    };
                }
            }
            i += 1;
        }

        
        let ghost final_nums = arr@;

        
        proof {
            assert forall|v: int|
                1 <= v <= n as int && #[trigger] Self::contains_value(nums@, v)
                implies final_nums[(v - 1)] as int == v
            by {
                assert(Self::contains_value(final_nums, v));
                let p = choose|p: int| 0 <= p < final_nums.len() && final_nums[p] as int == v;
                assert(final_nums[(final_nums[p] as int - 1)] == final_nums[p]);
            };
        }

        let mut k: usize = 0;
        while k < n
            invariant
                n == final_nums.len(),
                n <= 100_000,
                n == nums@.len(),
                0 <= k <= n,
                arr@ == final_nums,
                forall|v: int| #![auto]
                    Self::contains_value(final_nums, v) == Self::contains_value(nums@, v),
                forall|v: int|
                    1 <= v <= n as int && #[trigger] Self::contains_value(nums@, v)
                    ==> final_nums[(v - 1)] as int == v,
                
                forall|m: int| 0 <= m < k as int ==> final_nums[m] as int == m + 1,
                
                forall|v: int| 1 <= v <= k as int ==> Self::contains_value(nums@, v),
            decreases n - k,
        {
            if arr[k] != (k as i32) + 1 {
                proof {
                    if Self::contains_value(nums@, (k as int + 1)) {
                        
                        
                        assert(final_nums[k as int] as int == (k as int + 1));
                        assert(false);
                    }
                }
                return (k as i32) + 1;
            }
            proof {
                assert(final_nums[k as int] as int == (k as int + 1));
                assert(Self::contains_value(final_nums, (k as int + 1)));
                assert(Self::contains_value(nums@, (k as int + 1)));
            }
            k += 1;
        }

        
        proof {
            if Self::contains_value(nums@, (n as int + 1)) {
                assert(Self::contains_value(final_nums, (n as int + 1)));
                let wit = choose|p: int|
                    0 <= p < final_nums.len() && final_nums[p] as int == (n as int + 1);
                assert(final_nums[wit] as int == wit + 1);
                assert(false);
            }
        }
        (n as i32) + 1
    }
}

} 
