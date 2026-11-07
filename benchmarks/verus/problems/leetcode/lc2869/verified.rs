use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seen_in_suffix(nums: Seq<i32>, v: int, ops: int) -> bool {
        exists |q: int|
            0 <= q < ops
            && 0 <= nums.len() - ops + q < nums.len()
            && #[trigger] nums[nums.len() - ops + q] == v
    }

    pub open spec fn all_seen(nums: Seq<i32>, k: int, ops: int) -> bool {
        forall |v: int| 1 <= v <= k ==> Self::seen_in_suffix(nums, v, ops)
    }

    fn contains_in_suffix(nums: &Vec<i32>, ops: usize, v: i32) -> (found: bool)
        requires
            ops <= nums.len(),
        ensures
            found == Self::seen_in_suffix(nums@, v as int, ops as int),
    {
        let n = nums.len();
        let mut t: usize = 0;
        while t < ops
            invariant
                ops <= nums.len(),
                n == nums.len(),
                0 <= t <= ops,
                forall |q: int| 0 <= q < t as int ==> #[trigger] nums[n as int - ops as int + q] != v,
            decreases ops - t,
        {
            let idx = n - ops + t;
            if nums[idx] == v {
                proof {
                    assert(0 <= (t as int));
                    assert((t as int) < (ops as int));
                    assert(0 <= (n as int) - (ops as int) + (t as int));
                    assert((n as int) - (ops as int) + (t as int) < (n as int));
                    assert(nums[(n as int) - (ops as int) + (t as int)] == v);
                    assert(Self::seen_in_suffix(nums@, v as int, ops as int));
                }
                return true;
            }
            t = t + 1;
        }
        proof {
            assert forall |q: int| 0 <= q < ops as int implies #[trigger] nums[n as int - ops as int + q] != v by {
                assert(q < t as int);
            }
            assert(!Self::seen_in_suffix(nums@, v as int, ops as int));
        }
        false
    }

    pub fn min_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            1 <= k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
            Self::all_seen(nums@, k as int, nums.len() as int),
        ensures
            1 <= result <= nums.len(),
            Self::all_seen(nums@, k as int, result as int),
            forall |t: int| 1 <= t < result ==> !Self::all_seen(nums@, k as int, t),
    {
        let n = nums.len();
        let mut ops: usize = 1;
        while ops <= n
            invariant
                1 <= nums.len() <= 50,
                1 <= k <= nums.len(),
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
                Self::all_seen(nums@, k as int, nums.len() as int),
                n == nums.len(),
                1 <= ops <= n + 1,
                forall |t: int| 1 <= t < ops ==> !Self::all_seen(nums@, k as int, t),
            decreases n + 1 - ops,
        {
            let mut ok = true;
            assert(ops <= n);
            let mut v: i32 = 1;
            while v <= k
                invariant
                    1 <= v <= k + 1,
                    ops <= n,
                    n == nums.len(),
                    k <= 50,
                    ok == (forall |x: int| 1 <= x < v as int ==> Self::seen_in_suffix(nums@, x, ops as int)),
                decreases k + 1 - v,
            {
                let found = Self::contains_in_suffix(&nums, ops, v);
                if !found {
                    ok = false;
                }
                v = v + 1;
            }
            if ok {
                proof {
                    assert(Self::all_seen(nums@, k as int, ops as int));
                }
                return ops as i32;
            }
            ops = ops + 1;
        }
        n as i32
    }
}

}
