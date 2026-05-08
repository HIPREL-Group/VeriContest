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

    proof fn build_target_len(nums: Seq<i32>, index: Seq<i32>, step: int)
        requires
            0 <= step <= nums.len(),
            nums.len() == index.len(),
            forall |i: int| 0 <= i < index.len() ==> 0 <= #[trigger] index[i] <= i,
        ensures
            Self::build_target(nums, index, step).len() == step,
        decreases step,
    {
        if step > 0 {
            Self::build_target_len(nums, index, step - 1);
        }
    }

    proof fn insert_at_element(s: Seq<i32>, idx: int, val: i32, k: int)
        requires
            0 <= idx <= s.len(),
            0 <= k < s.len() + 1,
        ensures
            Self::insert_at(s, idx, val).len() == s.len() + 1,
            k < idx ==> Self::insert_at(s, idx, val)[k] == s[k],
            k == idx ==> Self::insert_at(s, idx, val)[k] == val,
            k > idx ==> Self::insert_at(s, idx, val)[k] == s[k - 1],
    {
        let result = Self::insert_at(s, idx, val);
        let prefix = s.subrange(0, idx);
        let mid = seq![val];
        let suffix = s.subrange(idx, s.len() as int);

        if k < idx {
            assert(result[k] == (prefix + mid + suffix)[k]);
            assert((prefix + mid)[k] == prefix[k]);
            assert(prefix[k] == s[k]);
        } else if k == idx {
            assert((prefix + mid)[k] == mid[0]);
        } else {
            assert(result[k] == (prefix + mid + suffix)[k]);
            assert((prefix + mid).len() == idx + 1);
            assert(result[k] == suffix[k - idx - 1]);
            assert(suffix[k - idx - 1] == s[k - 1]);
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

        while i < n
            invariant
                0 <= i <= n,
                n == nums.len(),
                n <= 100,
                nums.len() == index.len(),
                forall |k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100,
                forall |k: int| 0 <= k < index.len() ==> 0 <= #[trigger] index[k] <= k,
                target.len() == i,
                target@ == Self::build_target(nums@, index@, i as int),
            decreases n - i,
        {
            let idx = index[i] as usize;

            proof {
                Self::build_target_len(nums@, index@, i as int);
            }

            let ghost prev = target@;

            target.push(0i32);

            let mut j: usize = target.len() - 1;

            while j > idx
                invariant
                    0 <= idx <= j,
                    j <= i,
                    target.len() == i + 1,
                    i < n,
                    n <= 100,
                    prev.len() == i,
                    forall |k: int| 0 <= k < j ==> target[k] == prev[k],
                    forall |k: int| j < k && k <= i ==> target[k] == prev[k - 1],
                decreases j - idx,
            {
                target[j] = target[j - 1];
                j = j - 1;
            }

            target[idx] = nums[i];

            proof {
                let expected = Self::insert_at(prev, idx as int, nums@[i as int]);

                assert forall |k: int| 0 <= k < target.len() implies target@[k] == expected[k] by {
                    Self::insert_at_element(prev, idx as int, nums@[i as int], k);
                    if k < idx as int {
                    } else if k == idx as int {
                    } else {
                    }
                };

                assert(target@ =~= expected);
            }

            i = i + 1;
        }

        target
    }
}

}
