use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub open spec fn count_ones(s: Seq<i32>, end: int) -> int
            decreases end
        {
            if end <= 0 { 0 }
            else {
                Self::count_ones(s, end - 1) + if s[end - 1] == 1i32 { 1int } else { 0int }
            }
        }

        pub open spec fn circ_ones(s: Seq<i32>, start: int, w: int) -> int
            decreases w
        {
            if w <= 0 { 0 }
            else {
                Self::circ_ones(s, start, w - 1) + if s[(start + w - 1) % (s.len() as int)] == 1i32 { 1int } else { 0int }
            }
        }

        pub open spec fn max_circ_ones(s: Seq<i32>, w: int, pos: int) -> int
            decreases pos
        {
            if pos <= 0 {
                Self::circ_ones(s, 0, w)
            } else {
                let prev = Self::max_circ_ones(s, w, pos - 1);
                let cur = Self::circ_ones(s, pos, w);
                if cur > prev { cur } else { prev }
            }
        }

        proof fn count_ones_bounds(s: Seq<i32>, end: int)
            requires
                0 <= end <= s.len(),
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
            ensures
                0 <= Self::count_ones(s, end) <= end,
            decreases end
        {
            if end > 0 {
                Self::count_ones_bounds(s, end - 1);
            }
        }

        proof fn count_ones_positive(s: Seq<i32>, end: int)
            requires
                0 < end <= s.len(),
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
                exists|i: int| 0 <= i < end && s[i] == 1i32,
            ensures
                Self::count_ones(s, end) >= 1,
            decreases end
        {
            if s[end - 1] == 1i32 {
                Self::count_ones_bounds(s, end - 1);
            } else {
                let witness = choose|i: int| 0 <= i < end && s[i] == 1i32;
                assert(witness < end - 1);
                assert(exists|i: int| 0 <= i < end - 1 && s[i] == 1i32);
                Self::count_ones_positive(s, end - 1);
            }
        }

        proof fn circ_ones_bounds(s: Seq<i32>, start: int, w: int)
            requires
                s.len() > 0,
                w >= 0,
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
            ensures
                0 <= Self::circ_ones(s, start, w) <= w,
            decreases w
        {
            if w > 0 {
                Self::circ_ones_bounds(s, start, w - 1);
                let idx = (start + w - 1) % (s.len() as int);
                assert(0 <= idx < s.len() as int);
            }
        }

        proof fn circ_ones_first_positive(s: Seq<i32>, start: int, w: int)
            requires
                s.len() > 0,
                w >= 1,
                s[start % (s.len() as int)] == 1i32,
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
            ensures
                Self::circ_ones(s, start, w) >= 1,
            decreases w
        {
            if w == 1 {
                assert(Self::circ_ones(s, start, 1) == Self::circ_ones(s, start, 0) + if s[(start + 0) % (s.len() as int)] == 1i32 { 1int } else { 0int });
                assert((start + 0) % (s.len() as int) == start % (s.len() as int));
            } else {
                Self::circ_ones_first_positive(s, start, w - 1);
                let idx = (start + w - 1) % (s.len() as int);
                assert(0 <= idx < s.len() as int);
            }
        }

        proof fn circ_ones_slide(s: Seq<i32>, start: int, w: int)
            requires
                s.len() > 0,
                w >= 0,
                start >= 0,
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
            ensures
                Self::circ_ones(s, start + 1, w) == Self::circ_ones(s, start, w)
                    - if s[start % (s.len() as int)] == 1i32 { 1int } else { 0int }
                    + if s[(start + w) % (s.len() as int)] == 1i32 { 1int } else { 0int },
            decreases w
        {
            if w == 0 {
                assert(Self::circ_ones(s, start + 1, 0) == 0);
                assert(Self::circ_ones(s, start, 0) == 0);
                assert(start % (s.len() as int) == (start + 0) % (s.len() as int));
            } else {
                Self::circ_ones_slide(s, start, w - 1);
                let n = s.len() as int;
                assert(Self::circ_ones(s, start + 1, w) ==
                    Self::circ_ones(s, start + 1, w - 1) + if s[(start + 1 + w - 1) % n] == 1i32 { 1int } else { 0int });
                assert((start + 1 + w - 1) == (start + w));
                assert(Self::circ_ones(s, start, w) ==
                    Self::circ_ones(s, start, w - 1) + if s[(start + w - 1) % n] == 1i32 { 1int } else { 0int });
            }
        }

        proof fn max_circ_ones_bounds(s: Seq<i32>, w: int, pos: int)
            requires
                s.len() > 0,
                w >= 0,
                pos >= 0,
                forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 0i32 || s[i] == 1i32,
            ensures
                0 <= Self::max_circ_ones(s, w, pos) <= w,
            decreases pos
        {
            Self::circ_ones_bounds(s, 0, w);
            if pos > 0 {
                Self::max_circ_ones_bounds(s, w, pos - 1);
                Self::circ_ones_bounds(s, pos, w);
            }
        }

        pub fn min_swaps(nums: Vec<i32>) -> (res: i32)
            requires
                1 <= nums.len() <= 100000,
                forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
                exists|i: int| 0 <= i < nums.len() && nums[i] == 1,
            ensures
                res >= 0,
                res as int == Self::count_ones(nums@, nums.len() as int) - Self::max_circ_ones(nums@, Self::count_ones(nums@, nums.len() as int), nums.len() as int),
        {
            let mut total_ones: usize = 0;
            let mut i: usize = 0;
            while i < nums.len()
                invariant
                    0 <= i <= nums.len(),
                    nums.len() <= 100000,
                    forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == 0 || nums[k] == 1,
                    total_ones as int == Self::count_ones(nums@, i as int),
                    total_ones <= i,
                decreases nums.len() - i
            {
                if nums[i] == 1 {
                    total_ones = total_ones + 1;
                }
                i = i + 1;
            }

            proof {
                Self::count_ones_positive(nums@, nums.len() as int);
                Self::count_ones_bounds(nums@, nums.len() as int);
            }

            let window_size: usize = total_ones;
            let mut ones_in_window: usize = 0;

            i = 0;
            while i < window_size
                invariant
                    0 <= i <= window_size,
                    window_size == total_ones,
                    window_size as int == Self::count_ones(nums@, nums.len() as int),
                    1 <= window_size <= nums.len(),
                    nums.len() <= 100000,
                    forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == 0 || nums[k] == 1,
                    ones_in_window as int == Self::circ_ones(nums@, 0, i as int),
                    ones_in_window <= i,
                decreases window_size - i
            {
                proof {
                    let n = nums@.len() as int;
                    assert(n > 0);
                    assert((0 + i as int) % n == i as int) by (nonlinear_arith)
                        requires i as int >= 0, (i as int) < n, n > 0
                    {}
                }
                if nums[i] == 1 {
                    ones_in_window = ones_in_window + 1;
                }
                i = i + 1;
            }

            let mut max_ones = ones_in_window;

            let n = nums.len();
            i = 0;
            while i < n
                invariant
                    0 <= i <= n,
                    n == nums.len(),
                    n <= 100000,
                    n >= 1,
                    window_size == total_ones,
                    window_size as int == Self::count_ones(nums@, n as int),
                    1 <= window_size <= n,
                    forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == 0 || nums[k] == 1,
                    ones_in_window as int == Self::circ_ones(nums@, i as int, window_size as int),
                    max_ones as int == Self::max_circ_ones(nums@, window_size as int, i as int),
                    0 <= ones_in_window <= window_size,
                    0 <= max_ones <= window_size,
                decreases n - i
            {
                proof {
                    let si = i as int;
                    let w = window_size as int;
                    let sn = n as int;
                    assert(si < sn);
                    assert(si % sn == si) by (nonlinear_arith)
                        requires si >= 0, si < sn, sn > 0
                    {}
                    if nums@[si] == 1i32 {
                        Self::circ_ones_first_positive(nums@, si, w);
                    }
                }
                if nums[i] == 1 && ones_in_window > 0 {
                    ones_in_window = ones_in_window - 1;
                }
                assert(i < n);
                assert(window_size <= n);
                assert(i + window_size < 200000);
                let next_idx = (i + window_size) % n;
                if nums[next_idx] == 1 {
                    ones_in_window = ones_in_window + 1;
                }
                proof {
                    let si = i as int;
                    let w = window_size as int;
                    Self::circ_ones_slide(nums@, si, w);
                    assert(ones_in_window as int == Self::circ_ones(nums@, si + 1, w));
                }
                if ones_in_window > max_ones {
                    max_ones = ones_in_window;
                }
                proof {
                    let si = i as int;
                    let w = window_size as int;
                    assert(max_ones as int == Self::max_circ_ones(nums@, w, si + 1));
                    Self::circ_ones_bounds(nums@, si + 1, w);
                    Self::max_circ_ones_bounds(nums@, w, si + 1);
                }
                i = i + 1;
            }

            proof {
                Self::max_circ_ones_bounds(nums@, window_size as int, n as int);
            }

            if total_ones >= max_ones {
                (total_ones - max_ones) as i32
            } else {
                0i32
            }
        }
    }
}
