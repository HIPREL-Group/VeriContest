use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
        decreases len
    {
        if len <= 0 {
            0
        } else {
            nums[start] as int + Self::window_sum(nums, start + 1, len - 1)
        }
    }

    pub open spec fn min_two(a: int, b: int) -> int {
        if a == -1 {
            b
        } else if b == -1 {
            a
        } else if a <= b {
            a
        } else {
            b
        }
    }

    pub open spec fn window_candidate(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
    {
        let s = Self::window_sum(nums, start, len);
        if s > 0 { s } else { -1 }
    }

    pub open spec fn min_for_len_prefix(nums: Seq<i32>, len: int, count: int) -> int
        recommends
            1 <= len <= nums.len(),
            0 <= count <= nums.len() - len + 1,
        decreases count
    {
        if count <= 0 {
            -1
        } else {
            let prev = Self::min_for_len_prefix(nums, len, count - 1);
            let cand = Self::window_candidate(nums, count - 1, len);
            Self::min_two(prev, cand)
        }
    }

    pub open spec fn min_for_lengths_prefix(nums: Seq<i32>, l: int, upto: int) -> int
        recommends
            1 <= l <= nums.len(),
            l <= upto <= nums.len() + 1,
        decreases upto - l
    {
        if upto <= l {
            -1
        } else {
            let prev = Self::min_for_lengths_prefix(nums, l, upto - 1);
            let len = upto - 1;
            let all_starts = nums.len() - len + 1;
            let cur = Self::min_for_len_prefix(nums, len, all_starts);
            Self::min_two(prev, cur)
        }
    }

    proof fn lemma_min_two_assoc(a: int, b: int, c: int)
        ensures
            Self::min_two(Self::min_two(a, b), c) == Self::min_two(a, Self::min_two(b, c)),
    {
        if a == -1 {
        } else if b == -1 {
        } else if c == -1 {
        } else if a <= b {
            if a <= c {
            } else {
            }
        } else {
            if b <= c {
            } else {
            }
        }
    }

    proof fn lemma_window_sum_step(nums: Seq<i32>, start: int, len: int)
        requires
            0 <= start,
            1 <= len,
            start + len <= nums.len(),
        ensures
            Self::window_sum(nums, start, len) == Self::window_sum(nums, start, len - 1) + nums[start + len - 1],
        decreases len,
    {
        if len == 1 {
            assert(Self::window_sum(nums, start, 0) == 0);
            assert(Self::window_sum(nums, start, 1) == nums[start] as int + Self::window_sum(nums, start + 1, 0));
        } else {
            Self::lemma_window_sum_step(nums, start + 1, len - 1);
        }
    }

    pub fn minimum_sum_subarray(nums: Vec<i32>, l: i32, r: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            1 <= l <= r <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::min_for_lengths_prefix(nums@, l as int, r as int + 1),
    {
        let n = nums.len();
        let mut best: i64 = -1;
        let mut len: usize = l as usize;
        while len <= r as usize
            invariant
                n == nums.len(),
                1 <= n <= 100,
                1 <= l <= r <= nums.len(),
                forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
                l as usize <= len <= r as usize + 1,
                best == -1 || 1 <= best <= 100000,
                best as int == Self::min_for_lengths_prefix(nums@, l as int, len as int),
            decreases r as usize + 1 - len,
        {
            let mut start: usize = 0;
            proof {
                reveal_with_fuel(Solution::min_for_len_prefix, 2);
                assert(Self::min_for_len_prefix(nums@, len as int, 0) == -1);
                assert(Self::min_two(Self::min_for_lengths_prefix(nums@, l as int, len as int), -1)
                    == Self::min_for_lengths_prefix(nums@, l as int, len as int));
            }
            while start + len <= n
                invariant
                    n == nums.len(),
                    1 <= n <= 100,
                    1 <= l <= r <= nums.len(),
                    forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
                    l as usize <= len <= r as usize,
                    0 <= start <= n - len + 1,
                    best == -1 || 1 <= best <= 100000,
                    best as int == Self::min_two(
                        Self::min_for_lengths_prefix(nums@, l as int, len as int),
                        Self::min_for_len_prefix(nums@, len as int, start as int),
                    ),
                decreases n - len + 1 - start,
            {
                let mut sum: i64 = 0;
                let mut t: usize = 0;
                while t < len
                    invariant
                        n == nums.len(),
                        1 <= n <= 100,
                        1 <= len <= n,
                        start + len <= n,
                        0 <= t <= len,
                        forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
                        sum as int == Self::window_sum(nums@, start as int, t as int),
                        -1000 * (t as int) <= sum as int <= 1000 * (t as int),
                    decreases len - t,
                {
                    proof {
                        Self::lemma_window_sum_step(nums@, start as int, t as int + 1);
                        assert(nums@[start as int + t as int] >= -1000);
                        assert(nums@[start as int + t as int] <= 1000);
                    }
                    sum = sum + nums[start + t] as i64;
                    t += 1;
                }
                let ghost old_best = best;
                if sum > 0 && (best == -1 || sum < best) {
                    best = sum;
                }
                proof {
                    assert(sum as int == Self::window_sum(nums@, start as int, len as int));
                    assert(-1000 * (len as int) <= sum as int <= 1000 * (len as int));
                    assert(1 <= len <= 100);
                    if sum > 0 {
                        assert(sum as int <= 1000 * (len as int));
                        assert(sum as int <= 100000) by (nonlinear_arith)
                            requires sum as int <= 1000 * (len as int), len as int <= 100;
                    }
                    let cand = Self::window_candidate(nums@, start as int, len as int);
                    if sum > 0 {
                        assert(cand == sum as int);
                    } else {
                        assert(cand == -1);
                    }

                    if sum > 0 && (old_best == -1 || sum < old_best) {
                        assert(best == sum);
                        assert(best as int == cand);
                        if old_best == -1 {
                            assert(Self::min_two(old_best as int, cand) == cand);
                        } else {
                            assert(cand < old_best as int);
                            assert(Self::min_two(old_best as int, cand) == cand);
                        }
                    } else {
                        assert(best == old_best);
                        if cand == -1 {
                            assert(Self::min_two(old_best as int, cand) == old_best as int);
                        } else {
                            assert(cand == sum as int);
                            assert(!(old_best == -1 || sum < old_best));
                            assert(old_best != -1);
                            assert(old_best as int <= cand);
                            assert(Self::min_two(old_best as int, cand) == old_best as int);
                        }
                    }
                    assert(best as int == Self::min_two(old_best as int, cand));
                    assert(old_best as int == Self::min_two(
                        Self::min_for_lengths_prefix(nums@, l as int, len as int),
                        Self::min_for_len_prefix(nums@, len as int, start as int),
                    ));
                    reveal_with_fuel(Solution::min_for_len_prefix, 2);
                    assert(Self::min_for_len_prefix(nums@, len as int, start as int + 1) == Self::min_two(
                        Self::min_for_len_prefix(nums@, len as int, start as int),
                        cand,
                    ));
                    Self::lemma_min_two_assoc(
                        Self::min_for_lengths_prefix(nums@, l as int, len as int),
                        Self::min_for_len_prefix(nums@, len as int, start as int),
                        cand,
                    );
                    assert(best as int == Self::min_two(
                        Self::min_for_lengths_prefix(nums@, l as int, len as int),
                        Self::min_for_len_prefix(nums@, len as int, start as int + 1),
                    ));
                    if best != -1 {
                        assert(best <= 100000);
                    }
                }
                start += 1;
            }
            proof {
                assert(start + len > n);
                assert(start <= n - len + 1);
                if start <= n - len {
                    assert(start + len <= n);
                    assert(false);
                }
                assert(start == n - len + 1);
                reveal_with_fuel(Solution::min_for_lengths_prefix, 2);
                assert(Self::min_for_lengths_prefix(nums@, l as int, len as int + 1) == Self::min_two(
                    Self::min_for_lengths_prefix(nums@, l as int, len as int),
                    Self::min_for_len_prefix(nums@, len as int, (n - len + 1) as int),
                ));
                assert(best as int == Self::min_for_lengths_prefix(nums@, l as int, len as int + 1));
            }
            len += 1;
        }
        proof {
            assert(len == r as usize + 1);
            assert(best == -1 || 1 <= best <= 100000);
        }
        best as i32
    }
}

}
