use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn start_count(nums: Seq<i64>, m: int) -> int {
        if 0 < m <= nums.len() {
            nums.len() - m + 1
        } else {
            0
        }
    }

    pub open spec fn window_sum(nums: Seq<i64>, start: int, len: int) -> int
        decreases if len > 0 { len } else { 0 },
    {
        if len <= 0 || start < 0 || start + len > nums.len() {
            0
        } else {
            Self::window_sum(nums, start, len - 1) + nums[start + len - 1] as int
        }
    }

    pub open spec fn chosen_sum(nums: Seq<i64>, m: int, starts: Seq<int>) -> int
        decreases starts.len(),
    {
        if starts.len() == 0 {
            0
        } else {
            Self::window_sum(nums, starts[0], m) + Self::chosen_sum(nums, m, starts.drop_first())
        }
    }

    pub open spec fn admissible_from(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>) -> bool
    {
        &&& starts.len() == left
        &&& 0 <= left
        &&& 0 <= pos
        &&& 0 < m <= nums.len()
        &&& forall |i: int| 0 <= i < starts.len() ==> pos <= #[trigger] starts[i] < Self::start_count(nums, m)
        &&& forall |i: int, j: int| 0 <= i < j < starts.len() ==> #[trigger] starts[i] + m <= #[trigger] starts[j]
    }

    pub open spec fn admissible_starts(nums: Seq<i64>, m: int, k: int, starts: Seq<int>) -> bool
    {
        Self::admissible_from(nums, m, k, 0, starts)
    }

    pub open spec fn best_sum_from(nums: Seq<i64>, m: int, left: int, pos: int) -> int
        decreases if left > 0 { left } else { 0 }, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 },
    {
        if left <= 0 || pos < 0 {
            0
        } else if pos >= Self::start_count(nums, m) {
            -1
        } else {
            let skip = Self::best_sum_from(nums, m, left, pos + 1);
            let tail = Self::best_sum_from(nums, m, left - 1, pos + m);
            let take = if tail < 0 { -1 } else { Self::window_sum(nums, pos, m) + tail };
            if skip >= take { skip } else { take }
        }
    }

    proof fn lemma_window_sum_step(nums: Seq<i64>, start: int, len: int)
        requires
            0 <= start,
            1 <= len,
            start + len <= nums.len(),
        ensures
            Self::window_sum(nums, start, len)
                == Self::window_sum(nums, start, len - 1) + nums[start + len - 1] as int,
    {
        reveal_with_fuel(Solution::window_sum, 2);
    }

    proof fn lemma_window_sum_nonnegative(nums: Seq<i64>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            0 <= Self::window_sum(nums, start, len),
        decreases len,
    {
        if len > 0 {
            Self::lemma_window_sum_nonnegative(nums, start, len - 1);
            reveal_with_fuel(Solution::window_sum, 2);
            assert(0 <= nums[start + len - 1]);
        }
    }

    proof fn lemma_window_sum_bounded(nums: Seq<i64>, start: int, len: int)
        requires
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            Self::window_sum(nums, start, len) <= len * 1_000_000_000,
        decreases len,
    {
        if len > 0 {
            Self::lemma_window_sum_bounded(nums, start, len - 1);
            reveal_with_fuel(Solution::window_sum, 2);
        }
    }

    proof fn lemma_best_sum_bounded(nums: Seq<i64>, m: int, left: int, pos: int)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            -1 <= Self::best_sum_from(nums, m, left, pos),
            Self::best_sum_from(nums, m, left, pos) <= left * m * 1_000_000_000,
        decreases left, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 },
    {
        reveal_with_fuel(Solution::best_sum_from, 2);
        if left <= 0 || pos < 0 {
        } else if pos >= Self::start_count(nums, m) {
        } else {
            Self::lemma_best_sum_bounded(nums, m, left, pos + 1);
            Self::lemma_best_sum_bounded(nums, m, left - 1, pos + m);
            let tail = Self::best_sum_from(nums, m, left - 1, pos + m);
            if tail >= 0 {
                Self::lemma_window_sum_bounded(nums, pos, m);
                Self::lemma_window_sum_nonnegative(nums, pos, m);
                assert(Self::window_sum(nums, pos, m) + tail <= m * 1_000_000_000 + (left - 1) * m * 1_000_000_000);
                assert(m * 1_000_000_000 + (left - 1) * m * 1_000_000_000 == left * m * 1_000_000_000) by (nonlinear_arith)
                    requires m >= 1, left >= 1;
            }
        }
    }

    proof fn lemma_admissible_weaken_pos(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            Self::admissible_from(nums, m, left, pos + 1, starts),
        ensures
            Self::admissible_from(nums, m, left, pos, starts),
    {
        assert forall |i: int| 0 <= i < starts.len() implies pos <= #[trigger] starts[i] < Self::start_count(nums, m) by {
            assert(pos < pos + 1 <= starts[i]);
        }
    }

    proof fn lemma_admissible_shift_pos_if_first_gt(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>)
        requires
            0 < m <= nums.len(),
            0 < left,
            0 <= pos,
            Self::admissible_from(nums, m, left, pos, starts),
            starts[0] > pos,
        ensures
            Self::admissible_from(nums, m, left, pos + 1, starts),
    {
        assert forall |i: int| 0 <= i < starts.len() implies pos + 1 <= #[trigger] starts[i] < Self::start_count(nums, m) by {
            if i == 0 {
                assert(pos + 1 <= starts[0]);
            } else {
                assert(0 <= 0 < i < starts.len());
                assert(starts[0] + m <= starts[i]);
                assert(starts[0] >= pos + 1);
                assert(m >= 1);
                assert(pos + 1 <= starts[i]) by (nonlinear_arith)
                    requires
                        starts[0] >= pos + 1,
                        starts[0] + m <= starts[i],
                        m >= 1,
                ;
            }
        }
    }

    proof fn lemma_admissible_take_tail(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>)
        requires
            0 < m <= nums.len(),
            0 < left,
            0 <= pos,
            Self::admissible_from(nums, m, left, pos, starts),
            starts[0] == pos,
        ensures
            Self::admissible_from(nums, m, left - 1, pos + m, starts.drop_first()),
    {
        assert(starts.drop_first().len() == left - 1);
        assert forall |i: int| 0 <= i < starts.drop_first().len() implies pos + m <= #[trigger] starts.drop_first()[i] < Self::start_count(nums, m) by {
            assert(starts.drop_first()[i] == starts[i + 1]);
            assert(0 <= i + 1 < starts.len());
            assert(0 <= 0 < i + 1 < starts.len());
            assert(starts[0] + m <= starts[i + 1]);
        }
        assert forall |i: int, j: int| 0 <= i < j < starts.drop_first().len() implies #[trigger] starts.drop_first()[i] + m <= #[trigger] starts.drop_first()[j] by {
            assert(starts.drop_first()[i] == starts[i + 1]);
            assert(starts.drop_first()[j] == starts[j + 1]);
            assert(0 <= i + 1 < j + 1 < starts.len());
        }
    }

    proof fn lemma_admissible_prepend(nums: Seq<i64>, m: int, left: int, pos: int, tail: Seq<int>)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            pos < Self::start_count(nums, m),
            Self::admissible_from(nums, m, left, pos + m, tail),
        ensures
            Self::admissible_from(nums, m, left + 1, pos, seq![pos] + tail),
    {
        let starts = seq![pos] + tail;
        assert(starts.len() == left + 1);
        assert forall |i: int| 0 <= i < starts.len() implies pos <= #[trigger] starts[i] < Self::start_count(nums, m) by {
            if i == 0 {
                assert(starts[0] == pos);
            } else {
                assert(starts[i] == tail[i - 1]);
                assert(0 <= i - 1 < tail.len());
                assert(pos + m <= tail[i - 1]);
                assert(pos <= starts[i]);
            }
        }
        assert forall |i: int, j: int| 0 <= i < j < starts.len() implies #[trigger] starts[i] + m <= #[trigger] starts[j] by {
            if i == 0 {
                assert(starts[0] == pos);
                assert(starts[j] == tail[j - 1]);
                assert(0 <= j - 1 < tail.len());
                assert(pos + m <= tail[j - 1]);
            } else {
                assert(starts[i] == tail[i - 1]);
                assert(starts[j] == tail[j - 1]);
                assert(0 <= i - 1 < j - 1 < tail.len());
                assert(tail[i - 1] + m <= tail[j - 1]);
            }
        }
    }

    proof fn lemma_best_sum_nonnegative_when_feasible(nums: Seq<i64>, m: int, left: int, pos: int)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            pos + m * left <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            0 <= Self::best_sum_from(nums, m, left, pos),
        decreases left, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 },
    {
        if left > 0 {
            assert(pos + m <= nums.len()) by (nonlinear_arith)
                requires
                    pos + m * left <= nums.len(),
                    left >= 1,
                    m >= 1,
            ;
            assert(pos + m + m * (left - 1) <= nums.len()) by (nonlinear_arith)
                requires
                    pos + m * left <= nums.len(),
                    left >= 1,
                    m >= 1,
            ;
            Self::lemma_best_sum_nonnegative_when_feasible(nums, m, left - 1, pos + m);
            Self::lemma_window_sum_nonnegative(nums, pos, m);
            reveal_with_fuel(Solution::best_sum_from, 2);
        }
    }

    proof fn lemma_best_sum_exists_or_impossible(nums: Seq<i64>, m: int, left: int, pos: int)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            Self::best_sum_from(nums, m, left, pos) >= 0 ==> exists |starts: Seq<int>|
                Self::admissible_from(nums, m, left, pos, starts)
                && #[trigger] Self::chosen_sum(nums, m, starts) == Self::best_sum_from(nums, m, left, pos),
        decreases left, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 },
    {
        if left == 0 {
            reveal_with_fuel(Solution::best_sum_from, 2);
            assert(Self::admissible_from(nums, m, 0, pos, seq![]));
            assert(Self::chosen_sum(nums, m, seq![]) == 0);
        } else if pos >= Self::start_count(nums, m) {
            reveal_with_fuel(Solution::best_sum_from, 2);
        } else {
            reveal_with_fuel(Solution::best_sum_from, 2);
            let skip = Self::best_sum_from(nums, m, left, pos + 1);
            let tail = Self::best_sum_from(nums, m, left - 1, pos + m);
            let take = if tail < 0 { -1 } else { Self::window_sum(nums, pos, m) + tail };
            if skip >= take {
                if skip >= 0 {
                    Self::lemma_best_sum_exists_or_impossible(nums, m, left, pos + 1);
                    let witness = choose |starts: Seq<int>|
                        Self::admissible_from(nums, m, left, pos + 1, starts)
                        && Self::chosen_sum(nums, m, starts) == Self::best_sum_from(nums, m, left, pos + 1);
                    Self::lemma_admissible_weaken_pos(nums, m, left, pos, witness);
                    assert(Self::admissible_from(nums, m, left, pos, witness));
                    assert(Self::chosen_sum(nums, m, witness) == Self::best_sum_from(nums, m, left, pos));
                }
            } else {
                Self::lemma_best_sum_exists_or_impossible(nums, m, left - 1, pos + m);
                let tail_witness = choose |starts: Seq<int>|
                    Self::admissible_from(nums, m, left - 1, pos + m, starts)
                    && Self::chosen_sum(nums, m, starts) == Self::best_sum_from(nums, m, left - 1, pos + m);
                let witness = seq![pos] + tail_witness;
                Self::lemma_admissible_prepend(nums, m, left - 1, pos, tail_witness);
                assert(Self::admissible_from(nums, m, left, pos, witness));
                assert(witness.drop_first() == tail_witness);
                assert(witness[0] == pos);
                assert(Self::chosen_sum(nums, m, witness)
                    == Self::window_sum(nums, pos, m) + Self::chosen_sum(nums, m, tail_witness));
                assert(Self::chosen_sum(nums, m, tail_witness) == tail);
                assert(Self::chosen_sum(nums, m, witness) == take);
                assert(take == Self::best_sum_from(nums, m, left, pos));
            }
        }
    }

    proof fn lemma_chosen_sum_nonneg(nums: Seq<i64>, m: int, starts: Seq<int>)
        requires
            0 < m <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i] < Self::start_count(nums, m),
        ensures
            Self::chosen_sum(nums, m, starts) >= 0,
        decreases starts.len(),
    {
        if starts.len() > 0 {
            assert(0 <= starts[0] < Self::start_count(nums, m));
            assert(starts[0] + m <= nums.len());
            Self::lemma_window_sum_nonnegative(nums, starts[0], m);
            assert forall |i: int| 0 <= i < starts.drop_first().len() implies
                0 <= #[trigger] starts.drop_first()[i] < Self::start_count(nums, m) by {
                assert(starts.drop_first()[i] == starts[i + 1]);
            }
            Self::lemma_chosen_sum_nonneg(nums, m, starts.drop_first());
        }
    }

    proof fn lemma_best_sum_upper(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>)
        requires
            0 < m <= nums.len(),
            0 <= left,
            0 <= pos,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
            Self::admissible_from(nums, m, left, pos, starts),
        ensures
            Self::chosen_sum(nums, m, starts) <= Self::best_sum_from(nums, m, left, pos),
        decreases left, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 }, starts.len(),
    {
        if left == 0 {
            reveal_with_fuel(Solution::best_sum_from, 2);
            assert(starts.len() == 0);
            assert(Self::chosen_sum(nums, m, starts) == 0);
        } else if pos >= Self::start_count(nums, m) {
            assert(starts.len() == left);
            assert(left > 0);
            assert(0 <= starts[0] < starts.len());
            assert(pos <= starts[0] < Self::start_count(nums, m));
            assert(false);
        } else {
            let first = starts[0];
            if first == pos {
                Self::lemma_admissible_take_tail(nums, m, left, pos, starts);
                Self::lemma_best_sum_upper(nums, m, left - 1, pos + m, starts.drop_first());
                assert forall |i: int| 0 <= i < starts.drop_first().len() implies
                    0 <= #[trigger] starts.drop_first()[i] < Self::start_count(nums, m) by {
                    assert(starts.drop_first()[i] == starts[i + 1]);
                    assert(0 <= i + 1 < starts.len());
                }
                Self::lemma_chosen_sum_nonneg(nums, m, starts.drop_first());
                assert(Self::best_sum_from(nums, m, left - 1, pos + m) >= 0);
                reveal_with_fuel(Solution::best_sum_from, 2);
                assert(Self::chosen_sum(nums, m, starts)
                    == Self::window_sum(nums, pos, m) + Self::chosen_sum(nums, m, starts.drop_first()));
                assert(Self::chosen_sum(nums, m, starts.drop_first())
                    <= Self::best_sum_from(nums, m, left - 1, pos + m));
                assert(Self::window_sum(nums, pos, m) + Self::chosen_sum(nums, m, starts.drop_first())
                    <= Self::window_sum(nums, pos, m) + Self::best_sum_from(nums, m, left - 1, pos + m));
            } else {
                assert(first > pos);
                Self::lemma_admissible_shift_pos_if_first_gt(nums, m, left, pos, starts);
                Self::lemma_best_sum_upper(nums, m, left, pos + 1, starts);
                reveal_with_fuel(Solution::best_sum_from, 2);
                assert(Self::chosen_sum(nums, m, starts) <= Self::best_sum_from(nums, m, left, pos + 1));
            }
        }
    }

    pub fn max_k_segments_sum(nums: Vec<i64>, m: usize, k: usize) -> (result: i128)
        requires
            1 <= nums.len() <= 5000,
            1 <= m <= nums.len(),
            1 <= k,
            m * k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            exists |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                && result as int == #[trigger] Self::chosen_sum(nums@, m as int, starts),
            forall |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                    ==> #[trigger] Self::chosen_sum(nums@, m as int, starts) <= result as int,
    {
        let n = nums.len();
        let window_count = n - m + 1;

        let mut window_sums: Vec<i128> = Vec::new();
        let mut start: usize = 0;
        while start < window_count
            invariant
                0 <= start <= window_count <= n <= 5000,
                window_count + m == n + 1,
                nums.len() == n,
                window_sums.len() == start,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
                forall |j: int| 0 <= j < start ==> window_sums@[j] as int == #[trigger] Self::window_sum(nums@, j, m as int)
                    && 0 <= window_sums@[j] <= 1_000_000_000i128 * m as i128,
            decreases window_count - start,
        {
            let mut current: i128 = 0;
            let mut i: usize = 0;
            while i < m
                invariant
                    0 <= start < window_count <= n <= 5000,
                    window_count + m == n + 1,
                    0 <= i <= m,
                    nums.len() == n,
                    forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
                    current as int == Self::window_sum(nums@, start as int, i as int),
                    0 <= current as int <= 1_000_000_000 * i as int,
                decreases m - i,
            {
                proof {
                    assert(start + i < n) by (nonlinear_arith)
                        requires
                            start < window_count,
                            i < m,
                            window_count + m == n + 1,
                    ;
                    Self::lemma_window_sum_step(nums@, start as int, i as int + 1);
                    assert(current as int + nums@[start as int + i as int] <= 1_000_000_000 * (i as int + 1));
                }
                current = current + nums[start + i] as i128;
                i = i + 1;
            }
            window_sums.push(current);
            proof {
                assert forall |j: int| 0 <= j < start as int + 1 implies window_sums@[j] as int == #[trigger] Self::window_sum(nums@, j, m as int)
                    && 0 <= window_sums@[j] <= 1_000_000_000i128 * m as i128 by {
                    if j < start as int {
                    } else {
                        assert(j == start as int);
                    }
                }
            }
            start = start + 1;
        }

        let mut i: usize = 0;
        let mut prev: Vec<i128> = Vec::new();
        i = 0;
        while i <= n
            invariant
                0 <= i <= n + 1 <= 5001,
                prev.len() == i,
                forall |j: int| 0 <= j < i ==> prev@[j] == 0,
            decreases n + 1 - i,
        {
            prev.push(0);
            i = i + 1;
        }

        proof {
            assert(k <= n) by (nonlinear_arith)
                requires m >= 1, m * k <= n;
            reveal_with_fuel(Solution::best_sum_from, 1);
            assert forall |j: int| 0 <= j <= n as int implies prev@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, 0, j)
                && -1 <= prev@[j] <= 0 * (m as int) * 1_000_000_000 by {
            }
        }
        let mut taken: usize = 1;
        while taken <= k
            invariant
                1 <= taken <= k + 1 <= n + 1 <= 5001,
                1 <= m <= n <= 5000,
                m * k <= n,
                nums.len() == n,
                window_sums.len() == window_count,
                window_count + m == n + 1,
                prev.len() == n + 1,
                forall |j: int| 0 <= j < window_count ==> window_sums@[j] as int == #[trigger] Self::window_sum(nums@, j, m as int)
                    && 0 <= window_sums@[j] <= 1_000_000_000i128 * m as i128,
                forall |j: int| 0 <= j <= n ==> prev@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, taken as int - 1, j)
                    && -1 <= prev@[j] <= (taken as int - 1) * (m as int) * 1_000_000_000,
                forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases k + 1 - taken,
        {
            let mut curr: Vec<i128> = Vec::new();
            i = 0;
            while i <= n
                invariant
                    0 <= i <= n + 1 <= 5001,
                    curr.len() == i,
                    forall |j: int| 0 <= j < i ==> curr@[j] == -1,
                decreases n + 1 - i,
            {
                curr.push(-1);
                i = i + 1;
            }
            let mut idx: usize = n;
            proof {
                reveal_with_fuel(Solution::best_sum_from, 2);
                assert(curr@[n as int] as int == Self::best_sum_from(nums@, m as int, taken as int, n as int));
                Self::lemma_best_sum_bounded(nums@, m as int, taken as int, n as int);
                assert(-1 <= curr@[n as int] <= taken as int * (m as int) * 1_000_000_000);
            }
            while idx > 0
                invariant
                    nums.len() == n,
                    1 <= m <= n <= 5000,
                    1 <= taken <= k,
                    m * k <= n,
                    window_sums.len() == window_count,
                    window_count + m == n + 1,
                    prev.len() == n + 1,
                    curr.len() == n + 1,
                    0 <= idx <= n,
                    forall |j: int| 0 <= j < window_count ==> window_sums@[j] as int == #[trigger] Self::window_sum(nums@, j, m as int)
                        && 0 <= window_sums@[j] <= 1_000_000_000i128 * m as i128,
                    forall |j: int| 0 <= j <= n ==> prev@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, taken as int - 1, j)
                        && -1 <= prev@[j] <= (taken as int - 1) * (m as int) * 1_000_000_000,
                    forall |j: int| idx <= j <= n ==> curr@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, taken as int, j)
                        && -1 <= curr@[j] <= taken as int * (m as int) * 1_000_000_000,
                    forall |j: int| 0 <= j < nums.len() ==> 0 <= #[trigger] nums[j] <= 1_000_000_000,
                decreases idx,
            {
                let pos = idx - 1;
                let skip = curr[pos + 1];
                let take: i128;
                if m <= n - pos {
                    let tail = prev[pos + m];
                    if tail < 0 || pos >= window_count {
                        take = -1;
                    } else {
                        proof {
                            assert(window_sums@[pos as int] as int == Self::window_sum(nums@, pos as int, m as int));
                            assert(0 <= window_sums@[pos as int] <= 1_000_000_000i128 * m as i128);
                            assert(prev@[(pos + m) as int] as int == Self::best_sum_from(nums@, m as int, taken as int - 1, (pos + m) as int));
                            assert(0 <= tail <= (taken as int - 1) * (m as int) * 1_000_000_000);
                            assert(k as int <= n as int) by (nonlinear_arith)
                                requires m as int >= 1, m as int * k as int <= n as int;
                            assert(taken as int * (m as int) * 1_000_000_000 <= 5000 * 5000 * 1_000_000_000) by (nonlinear_arith)
                                requires taken <= k, k <= n, n <= 5000, m <= n;
                            assert(window_sums@[pos as int] as int + tail as int
                                <= 1_000_000_000 * m as int + (taken as int - 1) * (m as int) * 1_000_000_000);
                            assert(1_000_000_000 * m as int + (taken as int - 1) * (m as int) * 1_000_000_000
                                == taken as int * (m as int) * 1_000_000_000) by (nonlinear_arith)
                                requires m >= 1, taken >= 1;
                        }
                        take = window_sums[pos] + tail;
                    }
                } else {
                    take = -1;
                }
                let best = if skip >= take { skip } else { take };
                curr.set(pos, best);
                proof {
                    reveal_with_fuel(Solution::best_sum_from, 2);
                    assert(skip as int == Self::best_sum_from(nums@, m as int, taken as int, pos as int + 1));
                    if pos + m <= n {
                        let tail = prev[pos + m];
                        assert(tail as int == Self::best_sum_from(nums@, m as int, taken as int - 1, pos as int + m as int));
                        if tail < 0 || pos >= window_count {
                            assert(take as int == -1);
                        } else {
                            assert(window_sums@[pos as int] as int == Self::window_sum(nums@, pos as int, m as int));
                            assert(take as int == Self::window_sum(nums@, pos as int, m as int)
                                + Self::best_sum_from(nums@, m as int, taken as int - 1, pos as int + m as int));
                        }
                    } else {
                        assert(take as int == -1);
                    }
                    assert(best as int == Self::best_sum_from(nums@, m as int, taken as int, pos as int));
                    Self::lemma_best_sum_bounded(nums@, m as int, taken as int, pos as int);
                    assert(-1 <= best as int <= taken as int * (m as int) * 1_000_000_000);
                    assert forall |j: int| pos as int <= j <= n as int implies
                        curr@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, taken as int, j)
                        && -1 <= curr@[j] <= taken as int * (m as int) * 1_000_000_000 by {
                    };
                }
                idx = pos;
            }
            prev = curr;
            proof {
                assert forall |j: int| 0 <= j <= n as int implies
                    prev@[j] as int == #[trigger] Self::best_sum_from(nums@, m as int, taken as int, j)
                    && -1 <= prev@[j] <= taken as int * (m as int) * 1_000_000_000 by {
                };
            }
            taken = taken + 1;
        }

        let answer = prev[0];
        proof {
            assert(taken as int - 1 == k as int);
            assert(prev@[0] as int == Self::best_sum_from(nums@, m as int, k as int, 0));
            assert(answer as int == Self::best_sum_from(nums@, m as int, k as int, 0));
            Self::lemma_best_sum_nonnegative_when_feasible(nums@, m as int, k as int, 0);
            Self::lemma_best_sum_exists_or_impossible(nums@, m as int, k as int, 0);
            assert(exists |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                && answer as int == Self::chosen_sum(nums@, m as int, starts)) by {
                let witness = choose |starts: Seq<int>|
                    Self::admissible_from(nums@, m as int, k as int, 0, starts)
                    && Self::chosen_sum(nums@, m as int, starts) == Self::best_sum_from(nums@, m as int, k as int, 0);
                assert(Self::admissible_starts(nums@, m as int, k as int, witness));
            }
            assert forall |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                    implies #[trigger] Self::chosen_sum(nums@, m as int, starts) <= answer as int by {
                Self::lemma_best_sum_upper(nums@, m as int, k as int, 0, starts);
            }
        }
        answer
    }
}

}
