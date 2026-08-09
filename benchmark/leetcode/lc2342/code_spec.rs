use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_sum_spec(x: nat) -> nat
        decreases x,
    {
        if x == 0 {
            0
        } else {
            (x % 10) + Self::digit_sum_spec(x / 10)
        }
    }

    pub open spec fn valid_pair(nums: Seq<i32>, i: int, j: int) -> bool {
        0 <= i < j < nums.len()
            && Self::digit_sum_spec(nums[i] as nat) == Self::digit_sum_spec(nums[j] as nat)
    }
}

fn digit_sum_exec(x0: i32) -> (result: i64)
    requires 1 <= x0 <= 1_000_000_000,
    ensures result as nat == Solution::digit_sum_spec(x0 as nat),
        0 <= result <= 90,
{
    let mut x = x0;
    let mut s: i64 = 0;
    while x > 0 {
        s = s + (x % 10) as i64;
        x = x / 10;
    }
    s
}

impl Solution {
    pub fn maximum_sum(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
        ensures
            -1 <= result as int <= 2000000000,
            result == -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() ==> !(#[trigger] Self::valid_pair(nums@, i, j)),
            result != -1 ==> exists |i: int, j: int|
                0 <= i < j < nums.len()
                && Self::valid_pair(nums@, i, j)
                && result as int == nums[i] as int + nums[j] as int,
            result != -1 ==> forall |i: int, j: int|
                0 <= i < j < nums.len() && #[trigger] Self::valid_pair(nums@, i, j)
                ==> nums[i] as int + nums[j] as int <= result as int,
    {
        let n = nums.len();
        let mut max_bucket: Vec<i32> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 90 {
            max_bucket.push(-1);
            vi += 1;
        }

        let mut best: i32 = -1;
        let mut i: usize = 0;
        while i < n {
            let ds = digit_sum_exec(nums[i]);
            let dsu = ds as usize;
            let mx = max_bucket[dsu];
            if mx != -1 {
                let cand = nums[i] + mx;
                if best == -1 || cand > best {
                    best = cand;
                }
            }
            if mx == -1 || nums[i] > mx {
                max_bucket.set(dsu, nums[i]);
            }
            i += 1;
        }

        best
    }
}

}
