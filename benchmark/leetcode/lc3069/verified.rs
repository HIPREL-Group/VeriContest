use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn split_prefix(nums: Seq<i32>, n: int) -> Seq<Seq<i32>>
        decreases n,
    {
        if n <= 0 {
            seq![seq![], seq![]]
        } else if n == 1 {
            if nums.len() >= 1 {
                seq![seq![nums[0]], seq![]]
            } else {
                seq![seq![], seq![]]
            }
        } else if n == 2 {
            if nums.len() >= 2 {
                seq![seq![nums[0]], seq![nums[1]]]
            } else if nums.len() == 1 {
                seq![seq![nums[0]], seq![]]
            } else {
                seq![seq![], seq![]]
            }
        } else if n > nums.len() {
            Self::split_prefix(nums, nums.len() as int)
        } else {
            let prev = Self::split_prefix(nums, n - 1);
            let a1 = prev[0];
            let a2 = prev[1];
            if a1[a1.len() - 1] > a2[a2.len() - 1] {
                seq![a1.push(nums[n - 1]), a2]
            } else {
                seq![a1, a2.push(nums[n - 1])]
            }
        }
    }

    pub open spec fn append_prefix(a: Seq<i32>, b: Seq<i32>, n: int) -> Seq<i32>
        decreases n,
    {
        if n <= 0 {
            a
        } else {
            Self::append_prefix(a, b, n - 1).push(b[n - 1])
        }
    }

    pub open spec fn result_array_spec(nums: Seq<i32>) -> Seq<i32> {
        let parts = Self::split_prefix(nums, nums.len() as int);
        Self::append_prefix(parts[0], parts[1], parts[1].len() as int)
    }

    proof fn lemma_split_prefix_shape(nums: Seq<i32>, n: int)
        requires
            0 <= n <= nums.len(),
        ensures
            Self::split_prefix(nums, n).len() == 2,
            1 <= n ==> Self::split_prefix(nums, n)[0].len() > 0,
            2 <= n ==> Self::split_prefix(nums, n)[1].len() > 0,
        decreases n,
    {
        if n <= 2 {
        } else {
            Self::lemma_split_prefix_shape(nums, n - 1);
        }
    }

    pub fn result_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            result@ == Self::result_array_spec(nums@),
    {
        let n = nums.len();
        let mut arr1: Vec<i32> = Vec::new();
        let mut arr2: Vec<i32> = Vec::new();
        arr1.push(nums[0]);
        arr2.push(nums[1]);
        let mut i: usize = 2;
        while i < n
            invariant
                n == nums.len(),
                3 <= n <= 50,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                forall |k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] != nums[l],
                2 <= i <= n,
                Self::split_prefix(nums@, i as int).len() == 2,
                arr1@ == Self::split_prefix(nums@, i as int)[0],
                arr2@ == Self::split_prefix(nums@, i as int)[1],
                arr1.len() > 0,
                arr2.len() > 0,
            decreases n - i,
        {
            proof {
                Self::lemma_split_prefix_shape(nums@, i as int);
            }
            assert(i < nums.len());
            let last1 = arr1[arr1.len() - 1];
            let last2 = arr2[arr2.len() - 1];
            let ghost prev = Self::split_prefix(nums@, i as int);
            if arr1[arr1.len() - 1] > arr2[arr2.len() - 1] {
                arr1.push(nums[i]);
                proof {
                    assert(last1 == prev[0][prev[0].len() - 1]);
                    assert(last2 == prev[1][prev[1].len() - 1]);
                    assert(prev[0][prev[0].len() - 1] > prev[1][prev[1].len() - 1]);
                    assert((i + 1) as int <= nums.len() as int);
                    assert(Self::split_prefix(nums@, (i + 1) as int) == seq![prev[0].push(nums@[i as int]), prev[1]]);
                }
            } else {
                arr2.push(nums[i]);
                proof {
                    assert(last1 == prev[0][prev[0].len() - 1]);
                    assert(last2 == prev[1][prev[1].len() - 1]);
                    assert(prev[0][prev[0].len() - 1] <= prev[1][prev[1].len() - 1]);
                    assert((i + 1) as int <= nums.len() as int);
                    assert(Self::split_prefix(nums@, (i + 1) as int) == seq![prev[0], prev[1].push(nums@[i as int])]);
                }
            }
            i = i + 1;
        }
        let ghost parts = Self::split_prefix(nums@, n as int);
        let ghost base = parts[0];
        let mut result = arr1;
        let mut j: usize = 0;
        while j < arr2.len()
            invariant
                n == nums.len(),
                3 <= n <= 50,
                parts == Self::split_prefix(nums@, n as int),
                parts.len() == 2,
                base == parts[0],
                arr2@ == parts[1],
                0 <= j <= arr2.len(),
                result@ == Self::append_prefix(base, arr2@, j as int),
            decreases arr2.len() - j,
        {
            result.push(arr2[j]);
            proof {
                assert(Self::append_prefix(base, arr2@, (j + 1) as int)
                    == Self::append_prefix(base, arr2@, j as int).push(arr2[j as int]));
            }
            j = j + 1;
        }
        result
    }
}

}
