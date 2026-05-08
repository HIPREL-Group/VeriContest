use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn insert_at(s: Seq<i32>, idx: int, val: i32) -> Seq<i32> {
        s.subrange(0, idx) + seq![val] + s.subrange(idx, s.len() as int)
    }

    pub open spec fn build_target(nums: Seq<i32>, index: Seq<i32>, step: int) -> Seq<i32>
        decreases step,
    {
        if step <= 0 {
            Seq::<i32>::empty()
        } else {
            let prev = Self::build_target(nums, index, step - 1);
            Self::insert_at(prev, index[step - 1] as int, nums[step - 1])
        }
    }

    pub fn create_target_array(nums: Vec<i32>, index: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            nums.len() == index.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
            forall |i: int| 0 <= i < index.len() ==> 0 <= #[trigger] index[i] <= i,
        ensures
            result@ == Self::build_target(nums@, index@, nums.len() as int),
    {
        let n = nums.len();
        let mut target: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let idx = index[i] as usize;
            target.push(0i32);
            let mut j: usize = target.len() - 1;
            while j > idx {
                target[j] = target[j - 1];
                j = j - 1;
            }
            target[idx] = nums[i];
            i = i + 1;
        }
        target
    }
}

}
