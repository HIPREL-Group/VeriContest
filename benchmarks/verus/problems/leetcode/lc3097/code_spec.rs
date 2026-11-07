use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn imin(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn sub_or(nums: Seq<i32>, start: int, end: int) -> i32
        decreases end - start,
    {
        if end <= start {
            0i32
        } else {
            Self::sub_or(nums, start, end - 1) | nums[end - 1]
        }
    }

    pub open spec fn min_len_start_upto(nums: Seq<i32>, k: i32, start: int, upto: int) -> int
        decreases upto - start,
    {
        if upto <= start {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_start_upto(nums, k, start, upto - 1);
            let cand = if Self::sub_or(nums, start, upto) >= k {
                upto - start
            } else {
                nums.len() as int + 1
            };
            Self::imin(prev, cand)
        }
    }

    pub open spec fn min_len_prefix(nums: Seq<i32>, k: i32, processed: int) -> int
        decreases processed,
    {
        if processed <= 0 {
            nums.len() as int + 1
        } else {
            let prev = Self::min_len_prefix(nums, k, processed - 1);
            let cur = Self::min_len_start_upto(nums, k, processed - 1, nums.len() as int);
            Self::imin(prev, cur)
        }
    }

    pub open spec fn minimum_subarray_length_spec(nums: Seq<i32>, k: i32) -> int {
        let best = Self::min_len_prefix(nums, k, nums.len() as int);
        if best <= nums.len() as int { best } else { -1 }
    }
}

pub open spec fn bit_set(x: i32, b: u32) -> bool {
    (x >> b) & 1 == 1
}

fn bit_set_exec(x: i32, b: u32) -> (result: bool)
    requires 0 <= x, b < 30,
    ensures result == bit_set(x, b),
{
    (x >> b) & 1 == 1
}

impl Solution {
    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 200000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 1_000_000_000,
        ensures
            result as int == Self::minimum_subarray_length_spec(nums@, k),
    {
        let n = nums.len();

        let mut cnt: Vec<i32> = Vec::new();
        let mut bi: usize = 0;
        while bi < 30 {
            cnt.push(0);
            bi += 1;
        }

        let mut l: usize = 0;
        let mut r: usize = 0;
        let mut window_or: i32 = 0;
        let mut best: i32 = (n as i32) + 1;

        while l < n {
            while r < n && !(r > l && window_or >= k) {
                let old_r = r;
                let x = nums[r];
                let mut b: usize = 0;
                while b < 30 {
                    let bit_here = bit_set_exec(x, b as u32);
                    if bit_here {
                        cnt.set(b, cnt[b] + 1);
                    }
                    b += 1;
                }
                window_or = window_or | x;
                r += 1;
            }

            let old_best = best;
            if window_or >= k {
                let candidate: i32 = (r - l) as i32;
                if candidate < best {
                    best = candidate;
                } else {
                    best = old_best;
                }
            } else {
                best = old_best;
            }

            let removed = nums[l];
            let old_l = l;
            let mut b2: usize = 0;
            while b2 < 30 {
                let bit_here = bit_set_exec(removed, b2 as u32);
                if bit_here {
                    cnt.set(b2, cnt[b2] - 1);
                }
                b2 += 1;
            }

            let mut new_or: i32 = 0;
            let mut b3: usize = 0;
            while b3 < 30 {
                if cnt[b3] > 0 {
                    new_or = new_or | (1i32 << (b3 as u32));
                }
                b3 += 1;
            }
            window_or = new_or;
            l += 1;
        }

        if best <= n as i32 {
            best
        } else {
            -1
        }
    }
}

}
