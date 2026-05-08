use vstd::arithmetic::div_mod::lemma_mul_mod_noop;
use vstd::prelude::*;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct Solution;

impl Solution {
    pub const MOD: i64 = 1_000_000_007;

    pub open spec fn last_occurrence(nums: Seq<i32>, target: i32, upto: int) -> int
        decreases upto
    {
        if upto <= 0 {
            -1
        } else if nums[upto - 1] == target {
            upto - 1
        } else {
            Self::last_occurrence(nums, target, upto - 1)
        }
    }

    pub open spec fn close_block(nums: Seq<i32>, processed: int, frontier: int) -> int
        recommends
            0 <= processed <= nums.len(),
            -1 <= frontier < nums.len(),
        decreases nums.len() - processed
    {
        if processed >= nums.len() || processed > frontier {
            frontier
        } else {
            let last = Self::last_occurrence(nums, nums[processed], nums.len() as int);
            let new_frontier = if last > frontier { last } else { frontier };
            Self::close_block(nums, processed + 1, new_frontier)
        }
    }

    pub open spec fn block_end(nums: Seq<i32>, start: int) -> int
        recommends
            0 <= start < nums.len(),
    {
        let first = Self::last_occurrence(nums, nums[start], nums.len() as int);
        Self::close_block(nums, start + 1, first)
    }

    pub open spec fn number_of_good_partitions_from(nums: Seq<i32>, start: int) -> int
        recommends
            0 <= start <= nums.len(),
        decreases nums.len() - start
    {
        if start >= nums.len() {
            1
        } else {
            let next = Self::block_end(nums, start) + 1;
            if next <= start || next >= nums.len() {
                1
            } else {
                (2 * Self::number_of_good_partitions_from(nums, next)) % (Self::MOD as int)
            }
        }
    }

    pub open spec fn number_of_good_partitions_spec(nums: Seq<i32>) -> int {
        Self::number_of_good_partitions_from(nums, 0)
    }

    proof fn lemma_last_occurrence_at_least(nums: Seq<i32>, target: i32, idx: int, upto: int)
        requires
            0 <= idx < upto <= nums.len(),
            nums[idx] == target,
        ensures
            idx <= Self::last_occurrence(nums, target, upto),
        decreases upto - idx,
    {
        if upto != idx + 1 {
            if nums[upto - 1] == target {
            } else {
                Self::lemma_last_occurrence_at_least(nums, target, idx, upto - 1);
            }
        }
    }

    proof fn lemma_last_occurrence_bound(nums: Seq<i32>, target: i32, upto: int)
        requires
            0 <= upto <= nums.len(),
        ensures
            Self::last_occurrence(nums, target, upto) < upto,
        decreases upto,
    {
        if upto <= 0 {
        } else if nums[upto - 1] == target {
        } else {
            Self::lemma_last_occurrence_bound(nums, target, upto - 1);
        }
    }

    proof fn lemma_last_occurrence_is_target(nums: Seq<i32>, target: i32, upto: int)
        requires
            0 <= upto <= nums.len(),
            Self::last_occurrence(nums, target, upto) >= 0,
        ensures
            nums[Self::last_occurrence(nums, target, upto)] == target,
        decreases upto,
    {
        if upto <= 0 {
        } else if nums[upto - 1] == target {
        } else {
            Self::lemma_last_occurrence_is_target(nums, target, upto - 1);
        }
    }

    proof fn lemma_last_occurrence_agrees(nums: Seq<i32>, target: i32, idx: int, upto: int)
        requires
            0 <= idx < upto <= nums.len(),
            nums[idx] == target,
            forall|k: int| idx < k < upto ==> nums[k] != target,
        ensures
            Self::last_occurrence(nums, target, upto) == idx,
        decreases upto - idx,
    {
        if upto == idx + 1 {
        } else {
            assert(nums[upto - 1] != target);
            Self::lemma_last_occurrence_agrees(nums, target, idx, upto - 1);
        }
    }

    proof fn lemma_hashmap_matches_last_occurrence(nums: Seq<i32>, map: Map<i32, usize>, n: int)
        requires
            n == nums.len(),
            forall |v: i32| #[trigger] map.contains_key(v) ==> {
                let idx = map[v] as int;
                0 <= idx < n &&
                nums[idx] == v &&
                forall |k: int| idx < k < n ==> nums[k] != v
            },
            forall |i: int| 0 <= i < n ==> map.contains_key(#[trigger] nums[i]),
        ensures
            forall |v: i32| #[trigger] map.contains_key(v) ==>
                map[v] as int == Self::last_occurrence(nums, v, n),
    {
        assert forall |v: i32| #[trigger] map.contains_key(v) implies
            map[v] as int == Self::last_occurrence(nums, v, n) by {
            let idx = map[v] as int;
            Self::lemma_last_occurrence_agrees(nums, v, idx, n);
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn number_of_good_partitions(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            1 <= result < Self::MOD,
            result as int == Self::number_of_good_partitions_spec(nums@),
    {
        let n = nums.len();

        let mut last_map: std::collections::HashMap<i32, usize> = std::collections::HashMap::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= idx <= n,
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
                forall |v: i32| #[trigger] last_map@.contains_key(v) ==> {
                    let last_idx = last_map@[v] as int;
                    0 <= last_idx < idx &&
                    nums@[last_idx] == v &&
                    forall |k: int| last_idx < k < idx ==> nums@[k] != v
                },
                forall |i: int| 0 <= i < idx ==> last_map@.contains_key(#[trigger] nums@[i]),
            decreases n - idx,
        {
            let v = nums[idx];
            last_map.insert(v, idx);
            proof {
                assert forall |w: i32| #[trigger] last_map@.contains_key(w) implies ({
                    let last_idx = last_map@[w] as int;
                    0 <= last_idx < idx + 1 &&
                    nums@[last_idx] == w &&
                    forall |k: int| last_idx < k < idx + 1 ==> nums@[k] != w
                }) by {
                    if w == v {
                        assert(last_map@[w] == idx);
                    } else {
                    }
                }
                assert forall |i: int| 0 <= i < idx + 1 implies last_map@.contains_key(#[trigger] nums@[i]) by {
                    if i == idx as int {
                        assert(nums@[i] == v);
                        assert(last_map@.contains_key(v));
                    }
                }
            }
            idx += 1;
        }

        
        proof {
            Self::lemma_hashmap_matches_last_occurrence(nums@, last_map@, n as int);
        }

        let mut answer: i64 = 1;
        let mut start = 0usize;

        while start < n
            invariant
                n == nums.len(),
                1 <= n <= 100_000,
                0 <= start <= n,
                forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                1 <= answer < Self::MOD,
                ((answer as int) * Self::number_of_good_partitions_from(nums@, start as int))
                    % (Self::MOD as int) == Self::number_of_good_partitions_spec(nums@),
                
                forall |v: i32| #[trigger] last_map@.contains_key(v) ==> {
                    let last_idx = last_map@[v] as int;
                    0 <= last_idx < n &&
                    nums@[last_idx] == v &&
                    last_idx == Self::last_occurrence(nums@, v, n as int)
                },
                forall |i: int| 0 <= i < n ==> last_map@.contains_key(#[trigger] nums@[i]),
            decreases n - start,
        {
            let old_start = start;

            let mut end = *last_map.get(&nums[start]).unwrap();
            let mut i = start + 1;
            proof {
                assert(last_map@.contains_key(nums[start as int]));
                assert(end as int == Self::last_occurrence(nums@, nums[start as int], n as int));
                Self::lemma_last_occurrence_at_least(nums@, nums[start as int], start as int, n as int);
                assert(start as int <= end as int);
                assert(Self::close_block(nums@, i as int, end as int)
                    == Self::block_end(nums@, start as int));
            }
            while i < n && i <= end
                invariant
                    n == nums.len(),
                    1 <= n <= 100_000,
                    0 <= old_start < n,
                    old_start < i <= n,
                    old_start <= end < n,
                    forall |k: int| 0 <= k < n ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                    Self::close_block(nums@, i as int, end as int)
                        == Self::block_end(nums@, old_start as int),
                    forall |v: i32| #[trigger] last_map@.contains_key(v) ==> {
                        let last_idx = last_map@[v] as int;
                        0 <= last_idx < n &&
                        nums@[last_idx] == v &&
                        last_idx == Self::last_occurrence(nums@, v, n as int)
                    },
                    forall |ii: int| 0 <= ii < n ==> last_map@.contains_key(#[trigger] nums@[ii]),
                decreases n - i,
            {
                let old_end = end;

                let candidate = *last_map.get(&nums[i]).unwrap();
                if candidate > end {
                    end = candidate;
                }
                proof {
                    assert(last_map@.contains_key(nums[i as int]));
                    assert(candidate as int == Self::last_occurrence(nums@, nums[i as int], n as int));
                    let new_end = end as int;
                    let candidate_int = candidate as int;
                    if candidate > old_end {
                        assert(new_end == candidate_int);
                    } else {
                        assert(new_end == old_end as int);
                    }
                    assert(Self::close_block(nums@, i as int, old_end as int)
                        == Self::close_block(nums@, i as int + 1, new_end));
                }
                i += 1;
            }
            proof {
                assert(i as int > end as int);
                assert(Self::close_block(nums@, i as int, end as int) == end as int);
                assert(end as int == Self::block_end(nums@, old_start as int));
            }
            start = end + 1;
            if start < n {
                proof {
                    let suffix = Self::number_of_good_partitions_from(nums@, start as int);
                    assert(Self::number_of_good_partitions_from(nums@, old_start as int)
                        == (2 * suffix) % (Self::MOD as int));
                    lemma_mul_mod_noop(answer as int, 2 * suffix, Self::MOD as int);
                    lemma_mul_mod_noop(answer as int * 2, suffix, Self::MOD as int);
                    assert((((answer as int) * 2) * suffix)
                        == ((answer as int) * (2 * suffix))) by (nonlinear_arith);
                    assert(
                        ((((answer as int) * 2) % (Self::MOD as int)) * suffix)
                            % (Self::MOD as int)
                        == ((answer as int)
                            * Self::number_of_good_partitions_from(nums@, old_start as int))
                            % (Self::MOD as int)
                    );
                    assert(answer * 2 <= 2_000_000_012) by (nonlinear_arith)
                        requires
                            1 <= answer < Self::MOD,
                            Self::MOD == 1_000_000_007,
                    {};
                }
                answer = (answer * 2) % Self::MOD;
            } else {
                proof {
                    assert(Self::number_of_good_partitions_from(nums@, old_start as int) == 1);
                }
            }
        }

        proof {
            assert(Self::number_of_good_partitions_from(nums@, n as int) == 1);
            assert(answer as int == Self::number_of_good_partitions_spec(nums@));
            assert(answer < 2_147_483_647) by (nonlinear_arith)
                requires
                    1 <= answer < Self::MOD,
                    Self::MOD == 1_000_000_007,
            {};
        }
        answer as i32
    }
}

}
