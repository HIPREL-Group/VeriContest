use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_min_prefix(nums: Seq<i32>, j: int) -> i32
    recommends 0 <= j < nums.len()
    decreases j
{
    if j <= 0 {
        nums[0]
    } else if nums[j] < spec_min_prefix(nums, j - 1) {
        nums[j]
    } else {
        spec_min_prefix(nums, j - 1)
    }
}

proof fn lemma_min_prefix_le(nums: Seq<i32>, j: int, i: int)
    requires 0 <= i <= j, j < nums.len()
    ensures spec_min_prefix(nums, j) <= nums[i]
    decreases j
{
    if j == 0 {
    } else if i == j {
        if nums[j] < spec_min_prefix(nums, j - 1) {
        } else {
            lemma_min_prefix_le(nums, j - 1, i - 1);
        }
    } else {
        lemma_min_prefix_le(nums, j - 1, i);
    }
}

proof fn lemma_min_prefix_witness(nums: Seq<i32>, j: int) -> (w: int)
    requires 0 <= j, j < nums.len()
    ensures 0 <= w <= j, spec_min_prefix(nums, j) == nums[w]
    decreases j
{
    if j == 0 {
        0
    } else if nums[j] < spec_min_prefix(nums, j - 1) {
        j
    } else {
        lemma_min_prefix_witness(nums, j - 1)
    }
}

proof fn lemma_min_prefix_mono(nums: Seq<i32>, a: int, b: int)
    requires 0 <= a <= b, b < nums.len()
    ensures spec_min_prefix(nums, a) >= spec_min_prefix(nums, b)
    decreases b
{
    if a == b {
    } else {
        lemma_min_prefix_mono(nums, a, b - 1);
    }
}

pub struct Solution;

impl Solution {
    pub fn find132pattern(nums: Vec<i32>) -> (res: bool) 
        requires 
            1 <= nums.len() <= 20_000, 
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000, 
        ensures
            res == (exists |i: int, j: int, k: int| 
                0 <= i < j < k < nums.len() &&
                #[trigger] nums[i] < #[trigger] nums[k] < #[trigger] nums[j]), 
    {
        if nums.len() < 3 {
            proof {
                assert forall |i: int, j: int, k: int| 
                    0 <= i < j < k < nums.len() implies 
                    !(#[trigger] nums[i] < #[trigger] nums[k] < #[trigger] nums[j]) by {};
            }
            return false;
        }

        let mut min_left: Vec<i32> = Vec::new();
        min_left.push(nums[0]);
        
        let mut m: usize = 1;
        while m < nums.len()
            invariant
                1 <= nums.len() <= 20_000, 
                forall |idx: int| 0 <= idx < nums.len() ==> -1_000_000_000 <= #[trigger] nums[idx] <= 1_000_000_000,
                1 <= m <= nums.len(),
                min_left.len() == m,
                forall |j: int| 0 <= j < m ==> #[trigger] min_left[j] == spec_min_prefix(nums@, j),
            decreases nums.len() - m
        {
            let prev = min_left[m - 1];
            let curr = nums[m];
            if curr < prev {
                min_left.push(curr);
            } else {
                min_left.push(prev);
            }
            m += 1;
        }

        let mut stack: Vec<i32> = Vec::new();
        let ghost mut ghost_idxs: Seq<int> = Seq::empty();

        let mut j: usize = nums.len() - 1;

        while j > 0
            invariant
                3 <= nums.len() <= 20_000, 
                forall |idx: int| 0 <= idx < nums.len() ==> -1_000_000_000 <= #[trigger] nums[idx] <= 1_000_000_000,
                min_left.len() == nums.len(),
                forall |jj: int| 0 <= jj < nums.len() ==> #[trigger] min_left[jj] == spec_min_prefix(nums@, jj),
                0 <= j < nums.len(),
                stack.len() == ghost_idxs.len(),
                forall |id: int| 0 <= id < stack.len() ==> j < #[trigger] ghost_idxs[id] < nums.len(),
                forall |id: int| 0 <= id < stack.len() ==> #[trigger] stack[id] == nums[ghost_idxs[id]],
                forall |id: int| 0 <= id < stack.len() ==> #[trigger] stack[id] > min_left[j as int],
                forall |a: int, b: int| 0 <= a < b < stack.len() ==> #[trigger] stack[a] >= #[trigger] stack[b],
                forall |ii: int, jj: int, kk: int| 
                    0 <= ii < jj < kk < nums.len() && jj > j ==>
                    !(#[trigger] nums[ii] < #[trigger] nums[kk] < #[trigger] nums[jj]),
                forall |k: int| j < k < nums.len() && #[trigger] nums[k] > min_left[j as int] ==> 
                    (exists |id: int| 0 <= id < stack.len() && #[trigger] ghost_idxs[id] == k),
            decreases j
        {
            let current = nums[j];
            let l_min = min_left[j - 1];
            
            proof {
                lemma_min_prefix_mono(nums@, (j - 1) as int, j as int);
            }

            let ghost old_stack_view = stack@;
            let ghost old_ghost_idxs = ghost_idxs;
            
            
            while stack.len() > 0 && *stack.last().unwrap() <= l_min
                invariant
                    3 <= nums.len() <= 20_000,
                    forall |idx: int| 0 <= idx < nums.len() ==> -1_000_000_000 <= #[trigger] nums[idx] <= 1_000_000_000,
                    0 < j < nums.len(),
                    min_left.len() == nums.len(),
                    l_min == min_left[(j - 1) as int],
                    current == nums[j as int],
                    stack.len() == ghost_idxs.len(),
                    forall |id: int| 0 <= id < stack.len() ==> j < #[trigger] ghost_idxs[id] < nums.len(),
                    forall |id: int| 0 <= id < stack.len() ==> #[trigger] stack[id] == nums[ghost_idxs[id]],
                    forall |a: int, b: int| 0 <= a < b < stack.len() ==> #[trigger] stack[a] >= #[trigger] stack[b],
                    stack.len() <= old_stack_view.len(),
                    forall |id: int| 0 <= id < stack.len() ==> #[trigger] stack[id] == old_stack_view[id],
                    forall |id: int| 0 <= id < stack.len() ==> #[trigger] ghost_idxs[id] == old_ghost_idxs[id],
                    forall |old_id: int| 0 <= old_id < old_stack_view.len() && #[trigger] old_stack_view[old_id] > l_min ==> old_id < stack.len(),
                decreases stack.len()
            {
                stack.pop();
                proof { ghost_idxs = ghost_idxs.drop_last(); }
            }

            proof {
                assert forall |id: int| 0 <= id < stack.len() implies #[trigger] stack[id] > l_min by {
                    if stack.len() > 0 {
                        assert(stack[id] >= stack[stack.len() - 1]);
                    }
                };
            }

            if current > l_min {
                if stack.len() > 0 && *stack.last().unwrap() < current {
                    
                    proof {
                        let top = (stack.len() - 1) as int;
                        let k_idx = ghost_idxs[top];
                        let min_i = lemma_min_prefix_witness(nums@, (j - 1) as int);
                        assert(nums[min_i] == l_min);
                        assert(l_min < stack[top]);
                        assert(stack[top] == nums[k_idx]);
                        assert(nums[k_idx] < current);
                        assert(current == nums[j as int]);
                    }
                    return true;
                }
                
                stack.push(current);
                proof {
                    ghost_idxs = ghost_idxs.push(j as int);
                }
            }

            proof {
                assert forall |id: int| 0 <= id < stack.len() implies #[trigger] stack[id] > l_min by {
                    if current > l_min && id == stack.len() - 1 {
                    } 
                };

                assert forall |id: int| 0 <= id < stack.len() implies j - 1 < #[trigger] ghost_idxs[id] < nums.len() by {
                    if current > l_min && id == stack.len() - 1 {
                        assert(ghost_idxs[id] == j as int);
                    }
                };
                
                assert forall |id: int| 0 <= id < stack.len() implies #[trigger] stack[id] == nums[ghost_idxs[id]] by {
                    if current > l_min && id == stack.len() - 1 {
                        assert(ghost_idxs[id] == j as int);
                    }
                };
                
                assert forall |a: int, b: int| 0 <= a < b < stack.len() implies #[trigger] stack[a] >= #[trigger] stack[b] by {
                    if current > l_min && b == stack.len() - 1 && a < stack.len() - 1 {
                        let last_before = (stack.len() - 2) as int;
                        assert(stack[a] >= stack[last_before]);
                        assert(stack[last_before] >= current);
                    }
                };

                assert forall |ii: int, kk: int| 
                    0 <= ii < j && j < kk < nums.len() implies 
                    !(#[trigger] nums[ii] < #[trigger] nums[kk] && nums[kk] < nums[j as int]) by {
                    if nums[ii] < nums[kk] && nums[kk] < nums[j as int] {
                        lemma_min_prefix_le(nums@, (j-1) as int, ii);
                        assert(nums[ii] >= l_min);
                        assert(nums[kk] > l_min);
                        
                        if current <= l_min {
                            assert(nums[j as int] <= l_min);
                        } else {
                            lemma_min_prefix_mono(nums@, (j-1) as int, j as int);
                            assert(nums[kk] > min_left[j as int]);
                            let old_id = choose |id: int| 0 <= id < old_stack_view.len() && old_ghost_idxs[id] == kk;
                            assert(old_stack_view[old_id] == nums[kk]);
                            assert(old_stack_view[old_id] > l_min);
                            assert(old_id < stack.len() - 1);
                            assert(stack[old_id] == nums[kk]);
                            assert(stack[old_id] < current);
                            if stack.len() >= 2 {
                                let lb = (stack.len() - 2) as int;
                                assert(stack[lb] >= current);
                                assert(stack[lb] <= stack[old_id]);
                            }
                        }
                    }
                };
                
                assert forall |k: int| j - 1 < k < nums.len() && #[trigger] nums[k] > l_min implies 
                    (exists |id: int| 0 <= id < stack.len() && #[trigger] ghost_idxs[id] == k) by {
                    if k == j as int {
                        if current > l_min {
                            let new_id = (stack.len() - 1) as int;
                            assert(ghost_idxs[new_id] == k);
                        }
                    } else {
                        lemma_min_prefix_mono(nums@, (j-1) as int, j as int);
                        assert(nums[k] > min_left[j as int]);
                        let old_id = choose |id: int| 0 <= id < old_stack_view.len() && old_ghost_idxs[id] == k;
                        assert(old_stack_view[old_id] == nums[k]);
                        assert(old_stack_view[old_id] > l_min);
                        if current > l_min {
                            assert(old_id < stack.len() - 1);
                        } else {
                            assert(old_id < stack.len());
                        }
                        assert(ghost_idxs[old_id] == k);
                    }
                };
            }

            j -= 1;
        }
        
        proof {
            assert forall |i: int, j: int, k: int| 
                0 <= i < j < k < nums.len() implies 
                !(#[trigger] nums[i] < #[trigger] nums[k] < #[trigger] nums[j]) by {
            };
        }
        false
    }
}
}
