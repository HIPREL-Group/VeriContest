use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + 
                if s.last() == value { 1 as nat } else { 0 as nat}
        }
    }

    proof fn lemma_count_extend(s: Seq<i32>, value: i32, elem: i32)
        ensures
            Self::count_occurrences(s.push(elem), value) == 
                Self::count_occurrences(s, value) + if elem == value { 1 as nat } else { 0 as nat },
    {
        assert(s.push(elem).drop_last() =~= s);
    }

    proof fn lemma_count_at_least_one(s: Seq<i32>, value: i32, idx: int)
        requires
            0 <= idx < s.len(),
            s[idx] == value,
        ensures
            Self::count_occurrences(s, value) >= 1,
        decreases s.len()
    {
        if idx < s.len() - 1 {
            Self::lemma_count_at_least_one(s.drop_last(), value, idx);
        } else {
            assert(s.last() == value);
        }
    }

    pub fn most_frequent_even(nums: Vec<i32>) -> (res: i32) 
        requires 
            1 <= nums.len() <= 2_000, 
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        ensures 
            ((res == -1) && (forall |i: int| 0 <= i < nums.len() ==> nums[i] % 2 == 1)) || 
            ((res % 2 == 0) && (exists |j: int| 0 <= j < nums.len() && nums[j] == res) && (forall |i: int| 0 <= i < nums.len() && nums[i] % 2 == 0
                ==> ((Self::count_occurrences(nums@, nums[i]) < Self::count_occurrences(nums@, res)) || 
                (Self::count_occurrences(nums@, nums[i]) == Self::count_occurrences(nums@, res) && res <= nums[i])))),
    {
        let mut max_count = 0;
        let mut result: i32 = -1;
        
        for i in 0..nums.len() 
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 2_000, 
                forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
                max_count >= 0,
                (result == -1) <==> (max_count == 0),
                (result == -1 ==> forall |k: int| 0 <= k < i ==> nums[k] % 2 == 1),
                (result != -1 ==> 
                    result % 2 == 0 &&
                    exists |k: int| 0 <= k < i && nums[k] == result &&
                    max_count == Self::count_occurrences(nums@, result)
                ),
                forall |k: int| 0 <= k < i && nums[k] % 2 == 0 ==>
                    Self::count_occurrences(nums@, nums[k]) < max_count ||
                    (Self::count_occurrences(nums@, nums[k]) == max_count && result <= nums[k]),
        {
            if nums[i] % 2 == 0 {
                let mut count = 0;
                
                for j in 0..nums.len() 
                    invariant
                        0 <= i < nums.len(),
                        0 <= j <= nums.len(),
                        1 <= nums.len() <= 2_000, 
                        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
                        max_count >= 0,
                        (result == -1) <==> (max_count == 0),
                        (result == -1 ==> forall |k: int| 0 <= k < i ==> nums[k] % 2 == 1),
                        (result != -1 ==> 
                            result % 2 == 0 &&
                            exists |k: int| 0 <= k < i && nums[k] == result &&
                            max_count == Self::count_occurrences(nums@, result)
                        ),
                        forall |k: int| 0 <= k < i && nums[k] % 2 == 0 ==>
                            Self::count_occurrences(nums@, nums[k]) < max_count ||
                            (Self::count_occurrences(nums@, nums[k]) == max_count && result <= nums[k]),
                        nums[i as int] % 2 == 0,
                        count == Self::count_occurrences(nums@.subrange(0, j as int), nums[i as int]),
                        0 <= count <= j, 
                {
                    if nums[j] == nums[i] {
                        count += 1;
                    }

                    proof {
                        let old_j = j;
                        let prefix = nums@.subrange(0, old_j as int);
                        let new_prefix = nums@.subrange(0, (old_j + 1) as int);
                        
                        assert(new_prefix =~= prefix.push(nums[old_j as int]));
                        Self::lemma_count_extend(prefix, nums[i as int], nums[old_j as int]);
                    }
                }

                proof {
                    assert(nums@.subrange(0, nums.len() as int) =~= nums@);
                    Self::lemma_count_at_least_one(nums@, nums[i as int], i as int);
                }

                if count > max_count || (count == max_count && nums[i] < result) {
                    max_count = count;
                    result = nums[i] as i32;
                }
            }
        }
        
        result
    }
}

}
