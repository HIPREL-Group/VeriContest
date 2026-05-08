use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sub_spec(n: int) -> int
        decreases n
    {
        if n <= 0 || n % 2 == 0 {
            1
        } else {
            let m = n / 2;
            if m % 2 == 0 {
                1
            } else {
                2 * Self::sub_spec(m)
            }
        }
    }

    pub open spec fn min_one_spec(n: int) -> int {
        if n % 2 == 0 {
            -1
        } else {
            n - Self::sub_spec(n)
        }
    }

    pub open spec fn map_prefix(nums: Seq<i32>, i: int) -> Seq<i32>
        recommends
            0 <= i <= nums.len(),
        decreases i
    {
        if i <= 0 {
            seq![]
        } else {
            Self::map_prefix(nums, i - 1).push(Self::min_one_spec(nums[i - 1] as int) as i32)
        }
    }

    fn sub_one(n: i32) -> (s: i32)
        requires
            1 <= n <= 1000,
            n % 2 == 1,
        ensures
            s as int == Self::sub_spec(n as int),
            1 <= s <= n,
        decreases n
    {
        let m = n / 2;
        if m % 2 == 0 {
            1
        } else {
            let t = Self::sub_one(m);
            proof {
                assert(1 <= m <= 500);
                assert(1 <= t <= m);
                assert(2 * t <= 1000);
            }
            2 * t
        }
    }

    fn min_one(n: i32) -> (a: i32)
        requires
            2 <= n <= 1000,
        ensures
            a as int == Self::min_one_spec(n as int),
        decreases n
    {
        if n % 2 == 0 {
            -1
        } else {
            let s = Self::sub_one(n);
            proof {
                assert(1 <= s <= n);
            }
            n - s
        }
    }

    pub fn min_bitwise_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 2,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 1000,
        ensures
            result@ == Self::map_prefix(nums@, nums@.len() as int),
    {
        let mut ans = Vec::new();
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] >= 2,
                forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] <= 1000,
                ans@ == Self::map_prefix(nums@, i as int),
            decreases nums.len() - i
        {
            assert(2 <= nums[i as int] <= 1000);
            let a = Self::min_one(nums[i]);
            ans.push(a);
            proof {
                assert(ans@ == Self::map_prefix(nums@, i as int).push(a));
                assert(a as int == Self::min_one_spec(nums[i as int] as int));
                assert(Self::map_prefix(nums@, i as int + 1)
                    == Self::map_prefix(nums@, i as int).push(Self::min_one_spec(nums[i as int] as int) as i32));
            }
            i += 1;
        }
        ans
    }
}

}
