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
            decreases n - idx,
        {
            let v = nums[idx];
            last_map.insert(v, idx);
            
            idx += 1;
        }        

        let mut answer: i64 = 1;
        let mut start = 0usize;

        while start < n
            decreases n - start,
        {
            let old_start = start;

            let mut end = *last_map.get(&nums[start]).unwrap();
            let mut i = start + 1;
            
            while i < n && i <= end
                decreases n - i,
            {
                let old_end = end;

                let candidate = *last_map.get(&nums[i]).unwrap();
                if candidate > end {
                    end = candidate;
                }
                
                i += 1;
            }
            
            start = end + 1;
            if start < n {
                
                answer = (answer * 2) % Self::MOD;
            } else {
                
            }
        }

        
        answer as i32
    }
}

}
