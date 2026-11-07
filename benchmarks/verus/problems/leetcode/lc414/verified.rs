use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn third_max(nums: Vec<i32>) -> (res: i32) 
        requires
            1 <= nums.len() <= 10_000, 
            forall|i: int| 0 <= i < nums.len() ==> i32::MIN <= #[trigger] nums[i] <= i32::MAX,
        ensures 
            exists|i: int| 0 <= i < nums.len() && res == #[trigger] nums[i],
            (exists|a: int, b: int, c: int| 
                0 <= a < nums.len() && 0 <= b < nums.len() && 0 <= c < nums.len() &&
                #[trigger] nums[a] != #[trigger] nums[b] && #[trigger] nums[c] != nums[a] && nums[b] != nums[c]) ==>
            (
                exists|k: int| 0 <= k < nums.len() && res == #[trigger] nums[k] &&
                (exists|a: int, b: int| 0 <= a < nums.len() && 0 <= b < nums.len() &&
                    #[trigger] nums[a] > res && #[trigger] nums[b] > res && nums[a] != nums[b]) &&
                (forall|i: int| 0 <= i < nums.len() && #[trigger] nums[i] > res ==> 
                    (forall|j: int| 0 <= j < nums.len() && #[trigger] nums[j] > res && nums[i] != nums[j] ==>
                        (forall|k: int| 0 <= k < nums.len() && #[trigger] nums[k] > res ==>
                            nums[k] == nums[i] || nums[k] == nums[j])))
            ),
            (forall|a: int, b: int, c: int| 
                0 <= a < nums.len() && 0 <= b < nums.len() && 0 <= c < nums.len() ==>
                !(#[trigger] nums[a] != #[trigger] nums[b] && #[trigger] nums[c] != nums[a] && nums[b] != nums[c])) ==>
            (
                forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= res
            ),
    {
        let mut first: i32 = nums[0];
        let mut second: i32 = i32::MIN;
        let mut third: i32 = i32::MIN;
        let mut has_second = false;
        let mut has_third = false;
        
        let mut idx = 1;
        while idx < nums.len()
            invariant
                1 <= nums.len() <= 10_000, 
                forall|i: int| 0 <= i < nums.len() ==> i32::MIN <= #[trigger] nums[i] <= i32::MAX,
                1 <= idx <= nums.len(),
                exists|i: int| 0 <= i < idx && first == #[trigger] nums[i],
                has_second ==> exists|i: int| 0 <= i < idx && second == #[trigger] nums[i],
                has_third ==> exists|i: int| 0 <= i < idx && third == #[trigger] nums[i],
                has_third ==> has_second,
                has_third ==> first > second && second > third,
                has_second && !has_third ==> first > second,
                forall|j: int| 0 <= j < idx ==> #[trigger] nums[j] <= first,
                has_second ==> forall|j: int| 0 <= j < idx && #[trigger] nums[j] > second ==> nums[j] == first,
                !has_second ==> forall|j: int| 0 <= j < idx ==> #[trigger] nums[j] == first,
                (has_second && !has_third) ==> forall|j: int| 0 <= j < idx ==> 
                    #[trigger] nums[j] == first || nums[j] == second,
                has_third ==> forall|j: int| 0 <= j < idx && #[trigger] nums[j] > third ==> 
                    nums[j] == first || nums[j] == second,
            decreases nums.len() - idx,
        {
            let num = nums[idx];
            let old_first = first;
            let old_second = second;
            let old_third = third;
            let old_has_second = has_second;
            let old_has_third = has_third;
            
            if num > first {
                third = second;
                has_third = has_second;
                second = first;
                has_second = true;
                first = num;
            } else if num < first && (!has_second || num > second) {
                third = second;
                has_third = has_second;
                second = num;
                has_second = true;
            } else if has_second && num < second && (!has_third || num > third) {
                third = num;
                has_third = true;
            } 
            
            idx += 1;
        }
        
        if has_third {
            proof {
                let fi = choose|i: int| 0 <= i < nums.len() as int && first == #[trigger] nums[i];
                let si = choose|i: int| 0 <= i < nums.len() as int && second == #[trigger] nums[i];
                assert(nums[fi] > third);
                assert(nums[si] > third);
                assert(nums[fi] != nums[si]);
            }
            third
        } else {
            first
        }
    }
}

}