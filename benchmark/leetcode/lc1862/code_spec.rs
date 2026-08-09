use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn inner_sum(nums: Seq<i32>, i: int, end_j: int) -> int
    decreases end_j,
{
    if end_j <= 0 {
        0
    } else {
        inner_sum(nums, i, end_j - 1) + (nums[i] as int) / (nums[end_j - 1] as int)
    }
}

pub open spec fn outer_sum(nums: Seq<i32>, end_i: int) -> int
    decreases end_i,
{
    if end_i <= 0 {
        0
    } else {
        outer_sum(nums, end_i - 1) + inner_sum(nums, end_i - 1, nums.len() as int)
    }
}

impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        ensures
            result as int == outer_sum(nums@, nums.len() as int) % 1_000_000_007,
    {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;

        let mut count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000 {
            count.push(0);
            vi = vi + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            count.set(val, count[val] + 1);
            i = i + 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(count[0]);
        let mut v1: usize = 1;
        while v1 <= 100_000 {
            let next = prefix[v1 - 1] + count[v1];
            prefix.push(next);
            v1 = v1 + 1;
        }

        let mut gval: Vec<i64> = Vec::new();
        gval.push(0);
        let mut v2: usize = 1;
        while v2 <= 100_000 {
            let kmax_bound: usize = 100_000 / v2;
            let mut g: i64 = 0;
            let mut k: usize = 1;
            while k <= kmax_bound {
                let lo = k * v2;
                let k1 = k + 1;
                let hi_raw = k1 * v2 - 1;
                let hi: usize = if hi_raw > 100_000 { 100_000 } else { hi_raw };
                let range_count = prefix[hi] - prefix[lo - 1];
                g = g + (k as i64) * range_count;
                k = k + 1;
            }
            gval.push(g);
            v2 = v2 + 1;
        }

        let mut total: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let val = nums[j] as usize;
            total = (total + gval[val]) % modulo;
            j = j + 1;
        }
        (total % modulo) as i32
    }
}

}
