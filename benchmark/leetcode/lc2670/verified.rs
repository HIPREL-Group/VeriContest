use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn value_present(nums: Seq<i32>, left: int, right: int, v: nat) -> bool {
        exists |j: int| left <= j < right && nums[j] == v as i32
    }

    pub open spec fn count_distinct_upto(nums: Seq<i32>, left: int, right: int, upto: nat) -> nat
        decreases upto,
    {
        if upto == 0 {
            0
        } else {
            Self::count_distinct_upto(nums, left, right, (upto - 1) as nat)
                + if Self::value_present(nums, left, right, upto) { 1nat } else { 0nat }
        }
    }

    pub open spec fn distinct_count(nums: Seq<i32>, left: int, right: int) -> nat {
        Self::count_distinct_upto(nums, left, right, 50)
    }

    pub open spec fn distinct_diff_spec(nums: Seq<i32>, i: int) -> int {
        Self::distinct_count(nums, 0, i + 1) as int
            - Self::distinct_count(nums, i + 1, nums.len() as int) as int
    }

    fn count_distinct(nums: &Vec<i32>, left: usize, right: usize) -> (result: i32)
        requires
            left <= right <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            result as nat == Self::distinct_count(nums@, left as int, right as int),
            0 <= result <= 50,
    {
        let mut v: i32 = 1;
        let mut count: i32 = 0;
        while v <= 50
            invariant
                1 <= v <= 51,
                0 <= count,
                count <= v - 1,
                count as nat == Self::count_distinct_upto(nums@, left as int, right as int, (v - 1) as nat),
                left <= right <= nums.len(),
            decreases 51 - v,
        {
            let mut j: usize = left;
            let mut found: bool = false;
            while j < right
                invariant
                    left <= j <= right,
                    right <= nums.len(),
                    1 <= v <= 50,
                    found ==> Self::value_present(nums@, left as int, j as int, v as nat),
                    !found ==> forall |k: int| left as int <= k < j as int ==> nums@[k] != v,
                decreases right - j,
            {
                if nums[j] == v {
                    found = true;
                }
                j = j + 1;
            }
            proof {
                if found {
                    assert(Self::value_present(nums@, left as int, right as int, v as nat));
                } else {
                    assert(!Self::value_present(nums@, left as int, right as int, v as nat)) by {
                        if Self::value_present(nums@, left as int, right as int, v as nat) {
                            let k = choose |k: int| left as int <= k < right as int && nums[k] == v;
                            assert(left as int <= k < j as int);
                            assert(nums@[k] != v);
                            assert(false);
                        }
                    }
                }
            }
            if found {
                count = count + 1;
            }
            proof {
                assert((if Self::value_present(nums@, left as int, right as int, v as nat) { 1nat } else { 0nat }) <= 1nat);
                assert(Self::count_distinct_upto(nums@, left as int, right as int, v as nat)
                    == Self::count_distinct_upto(nums@, left as int, right as int, ((v - 1) as nat))
                        + if Self::value_present(nums@, left as int, right as int, v as nat) { 1nat } else { 0nat });
            }
            v = v + 1;
        }
        count
    }

    pub fn distinct_difference_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] result[i] == Self::distinct_diff_spec(nums@, i),
    {
        let n = nums.len();
        let mut out: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                1 <= n <= 50,
                n == nums.len(),
                out.len() == i,
                forall |k: int| 0 <= k < i ==> #[trigger] out[k] == Self::distinct_diff_spec(nums@, k),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
            decreases n - i,
        {
            let p = Self::count_distinct(&nums, 0, i + 1);
            let s = Self::count_distinct(&nums, i + 1, n);
            out.push(p - s);
            i = i + 1;
        }
        out
    }
}

}
