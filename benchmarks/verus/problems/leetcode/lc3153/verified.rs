use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit_count(n: int) -> int
        decreases n
    {
        if n <= 0 { 1 } else if n < 10 { 1 } else { 1 + Self::digit_count(n / 10) }
    }

    pub open spec fn digit_diff_count(a: int, b: int, pos: int) -> int
        decreases pos,
    {
        if pos <= 0 {
            0
        } else {
            Self::digit_diff_count(a / 10, b / 10, pos - 1)
                + if a % 10 != b % 10 { 1int } else { 0int }
        }
    }

    pub open spec fn pair_sum_for_i(nums: Seq<i32>, i: int, j: int) -> int
        decreases j,
    {
        if j <= 0 {
            0
        } else {
            Self::pair_sum_for_i(nums, i, j - 1)
                + Self::digit_diff_count(nums[i] as int, nums[j - 1] as int, 9)
        }
    }

    pub open spec fn all_pair_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::all_pair_sum(nums, end - 1) + Self::pair_sum_for_i(nums, end - 1, end - 1)
        }
    }

    pub open spec fn sum_digit_differences_spec(nums: Seq<i32>, result: int) -> bool {
        &&& 2 <= nums.len() <= 100000
        &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000
        &&& forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
            ==> Self::digit_count(#[trigger] nums[i] as int) == Self::digit_count(#[trigger] nums[j] as int)
        &&& result == Self::all_pair_sum(nums, nums.len() as int)
    }

    proof fn lemma_digit_diff_count_bounds(a: int, b: int, pos: int)
        requires
            0 <= pos <= 9,
        ensures
            0 <= Self::digit_diff_count(a, b, pos) <= pos,
        decreases pos,
    {
        if pos > 0 {
            Self::lemma_digit_diff_count_bounds(a / 10, b / 10, pos - 1);
        }
    }

    proof fn lemma_pair_sum_for_i_bound(nums: Seq<i32>, i: int, j: int)
        requires
            0 <= j <= i < nums.len(),
        ensures
            0 <= Self::pair_sum_for_i(nums, i, j) <= 9 * j,
        decreases j,
    {
        if j > 0 {
            Self::lemma_pair_sum_for_i_bound(nums, i, j - 1);
            Self::lemma_digit_diff_count_bounds(nums[i] as int, nums[j - 1] as int, 9);
        }
    }

    proof fn lemma_all_pair_sum_bound(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
            end <= 100000,
        ensures
            0 <= Self::all_pair_sum(nums, end),
            Self::all_pair_sum(nums, end) <= 9 * end * end,
            Self::all_pair_sum(nums, end) <= 90_000_000_000,
        decreases end,
    {
        if end > 0 {
            assert(end >= 1);
            Self::lemma_all_pair_sum_bound(nums, end - 1);
            Self::lemma_pair_sum_for_i_bound(nums, end - 1, end - 1);
            assert(Self::all_pair_sum(nums, end)
                == Self::all_pair_sum(nums, end - 1) + Self::pair_sum_for_i(nums, end - 1, end - 1));
            assert(Self::pair_sum_for_i(nums, end - 1, end - 1) <= 9 * (end - 1));
            assert(Self::all_pair_sum(nums, end - 1) <= 9 * (end - 1) * (end - 1));
            assert(Self::all_pair_sum(nums, end) <= 9 * (end - 1) * (end - 1) + 9 * (end - 1));
            assert(9 * (end - 1) * (end - 1) + 9 * (end - 1) <= 9 * end * end)
                by (nonlinear_arith)
                requires end >= 1;
            assert(Self::all_pair_sum(nums, end) <= 9 * end * end);
        }
        assert(end >= 0);
        assert(end <= 100000);
        assert(0 <= end <= 100000);
        assert(9 * end * end <= 90_000_000_000)
            by (nonlinear_arith)
            requires 0 <= end <= 100000;
        assert(Self::all_pair_sum(nums, end) <= 90_000_000_000);
    }

    fn digit_diff_count_exec(a: i32, b: i32, pos: usize) -> (res: i64)
        requires
            0 <= pos <= 9,
            0 <= a < 1_000_000_000,
            0 <= b < 1_000_000_000,
        ensures
            res as int == Self::digit_diff_count(a as int, b as int, pos as int),
            0 <= res <= pos as int,
        decreases pos,
    {
        if pos == 0 {
            0
        } else {
            let next = Self::digit_diff_count_exec(a / 10, b / 10, pos - 1);
            let add = if a % 10 != b % 10 { 1i64 } else { 0i64 };
            assert(Self::digit_diff_count(a as int, b as int, pos as int)
                == Self::digit_diff_count((a / 10) as int, (b / 10) as int, (pos - 1) as int)
                    + if (a as int) % 10 != (b as int) % 10 { 1int } else { 0int });
            assert((a / 10) as int == (a as int) / 10);
            assert((b / 10) as int == (b as int) / 10);
            assert((a % 10) as int == (a as int) % 10);
            assert((b % 10) as int == (b as int) % 10);
            next + add
        }
    }

    fn pair_sum_for_i_exec(nums: &Vec<i32>, i: usize, j: usize) -> (res: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] < 1_000_000_000,
            i < nums.len(),
            j <= i,
        ensures
            res as int == Self::pair_sum_for_i(nums@, i as int, j as int),
            0 <= res,
            res as int <= 9 * (j as int),
        decreases j,
    {
        if j == 0 {
            0
        } else {
            let prev = Self::pair_sum_for_i_exec(nums, i, j - 1);
            let diff = Self::digit_diff_count_exec(nums[i], nums[j - 1], 9);
            assert(j > 0);
            assert((j - 1) as int == j as int - 1);
            assert(prev as int <= 9 * ((j - 1) as int));
            assert(diff as int <= 9);
            assert((prev as int) + (diff as int) <= 9 * ((j - 1) as int) + 9);
            assert(9 * ((j - 1) as int) + 9 == 9 * (j as int)) by (nonlinear_arith);
            assert(j <= 100000);
            assert(j as int <= 100000);
            assert(0 <= j as int <= 100000);
            assert(9 * (j as int) <= 900000)
                by (nonlinear_arith)
                requires 0 <= j as int <= 100000;
            assert(900000int <= i64::MAX);
            assert(prev + diff <= i64::MAX);
            assert(Self::pair_sum_for_i(nums@, i as int, j as int)
                == Self::pair_sum_for_i(nums@, i as int, (j - 1) as int)
                    + Self::digit_diff_count(nums@[i as int] as int, nums@[(j - 1) as int] as int, 9));
            prev + diff
        }
    }

    fn all_pair_sum_exec(nums: &Vec<i32>, end: usize) -> (res: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] < 1_000_000_000,
            end <= nums.len(),
        ensures
            res as int == Self::all_pair_sum(nums@, end as int),
            0 <= res,
        decreases end,
    {
        if end == 0 {
            0
        } else {
            let prev = Self::all_pair_sum_exec(nums, end - 1);
            let add = Self::pair_sum_for_i_exec(nums, end - 1, end - 1);
            assert(end > 0);
            assert(end <= nums.len());
            assert(nums.len() <= 100000);
            assert(end <= 100000);
            assert((end - 1) as int <= 99999);
            proof {
                Self::lemma_all_pair_sum_bound(nums@, (end - 1) as int);
            }
            assert(prev as int <= 90_000_000_000);
            assert(add as int <= 9 * ((end - 1) as int));
            assert(end as int <= 100000);
            assert(0 <= (end - 1) as int <= 99999);
            assert(add as int <= 900000)
                by (nonlinear_arith)
                requires add as int <= 9 * ((end - 1) as int), 0 <= (end - 1) as int <= 99999;
            assert(prev >= 0);
            assert(prev as int <= i64::MAX);
            assert((prev as int) + (add as int) <= 90_000_000_000 + 900000);
            assert(90_000_000_000 + 900000 == 90_000_900_000);
            assert(90_000_900_000int <= i64::MAX);
            assert(prev + add <= i64::MAX);
            assert(Self::all_pair_sum(nums@, end as int)
                == Self::all_pair_sum(nums@, (end - 1) as int)
                    + Self::pair_sum_for_i(nums@, (end - 1) as int, (end - 1) as int));
            prev + add
        }
    }

}

pub open spec fn digit_at(n: int, p: int) -> int
    decreases p,
{
    if p <= 0 { n % 10 } else { digit_at(n / 10, p - 1) }
}

pub open spec fn ind_diff(a: int, b: int, p: int) -> int {
    if digit_at(a, p) != digit_at(b, p) { 1int } else { 0int }
}

pub open spec fn sum_ind_diff(a: int, b: int, upto: int) -> int
    decreases upto,
{
    if upto <= 0 { 0 } else { sum_ind_diff(a, b, upto - 1) + ind_diff(a, b, upto - 1) }
}

proof fn lemma_sum_ind_diff_shift(a: int, b: int, pos: int)
    requires pos > 0,
    ensures sum_ind_diff(a, b, pos) == ind_diff(a, b, 0) + sum_ind_diff(a / 10, b / 10, pos - 1),
    decreases pos,
{
    if pos == 1 {
        assert(sum_ind_diff(a, b, 1) == sum_ind_diff(a, b, 0) + ind_diff(a, b, 0));
        assert(sum_ind_diff(a, b, 0) == 0);
        assert(sum_ind_diff(a / 10, b / 10, 0) == 0);
    } else {
        lemma_sum_ind_diff_shift(a, b, pos - 1);
        assert(digit_at(a, pos - 1) == digit_at(a / 10, pos - 2));
        assert(digit_at(b, pos - 1) == digit_at(b / 10, pos - 2));
        assert(ind_diff(a, b, pos - 1) == ind_diff(a / 10, b / 10, pos - 2));
    }
}

proof fn lemma_digit_diff_count_eq_sum(a: int, b: int, pos: int)
    requires 0 <= pos,
    ensures Solution::digit_diff_count(a, b, pos) == sum_ind_diff(a, b, pos),
    decreases pos,
{
    if pos > 0 {
        lemma_digit_diff_count_eq_sum(a / 10, b / 10, pos - 1);
        lemma_sum_ind_diff_shift(a, b, pos);
        assert(digit_at(a, 0) == a % 10);
        assert(digit_at(b, 0) == b % 10);
    }
}

proof fn lemma_sum_ind_diff_unfold9(a: int, b: int)
    ensures sum_ind_diff(a, b, 9) == ind_diff(a, b, 0) + ind_diff(a, b, 1) + ind_diff(a, b, 2)
        + ind_diff(a, b, 3) + ind_diff(a, b, 4) + ind_diff(a, b, 5) + ind_diff(a, b, 6)
        + ind_diff(a, b, 7) + ind_diff(a, b, 8),
{
    assert(sum_ind_diff(a, b, 0) == 0);
    assert(sum_ind_diff(a, b, 1) == sum_ind_diff(a, b, 0) + ind_diff(a, b, 0));
    assert(sum_ind_diff(a, b, 2) == sum_ind_diff(a, b, 1) + ind_diff(a, b, 1));
    assert(sum_ind_diff(a, b, 3) == sum_ind_diff(a, b, 2) + ind_diff(a, b, 2));
    assert(sum_ind_diff(a, b, 4) == sum_ind_diff(a, b, 3) + ind_diff(a, b, 3));
    assert(sum_ind_diff(a, b, 5) == sum_ind_diff(a, b, 4) + ind_diff(a, b, 4));
    assert(sum_ind_diff(a, b, 6) == sum_ind_diff(a, b, 5) + ind_diff(a, b, 5));
    assert(sum_ind_diff(a, b, 7) == sum_ind_diff(a, b, 6) + ind_diff(a, b, 6));
    assert(sum_ind_diff(a, b, 8) == sum_ind_diff(a, b, 7) + ind_diff(a, b, 7));
    assert(sum_ind_diff(a, b, 9) == sum_ind_diff(a, b, 8) + ind_diff(a, b, 8));
}

pub open spec fn count_diff_at_pos(nums: Seq<i32>, i: int, j: int, p: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        count_diff_at_pos(nums, i, j - 1, p) + ind_diff(nums[i] as int, nums[j - 1] as int, p)
    }
}

proof fn lemma_pair_sum_decompose(nums: Seq<i32>, i: int, j: int)
    requires 0 <= j <= i < nums.len(),
    ensures Solution::pair_sum_for_i(nums, i, j) ==
        count_diff_at_pos(nums, i, j, 0) + count_diff_at_pos(nums, i, j, 1) + count_diff_at_pos(nums, i, j, 2)
        + count_diff_at_pos(nums, i, j, 3) + count_diff_at_pos(nums, i, j, 4) + count_diff_at_pos(nums, i, j, 5)
        + count_diff_at_pos(nums, i, j, 6) + count_diff_at_pos(nums, i, j, 7) + count_diff_at_pos(nums, i, j, 8),
    decreases j,
{
    if j > 0 {
        lemma_pair_sum_decompose(nums, i, j - 1);
        let a = nums[i] as int;
        let b = nums[j - 1] as int;
        lemma_digit_diff_count_eq_sum(a, b, 9);
        lemma_sum_ind_diff_unfold9(a, b);
        assert(Solution::pair_sum_for_i(nums, i, j)
            == Solution::pair_sum_for_i(nums, i, j - 1) + Solution::digit_diff_count(a, b, 9));
        assert forall |p: int| 0 <= p < 9 implies
            #[trigger] count_diff_at_pos(nums, i, j, p) == count_diff_at_pos(nums, i, j - 1, p) + ind_diff(a, b, p) by {}
    }
}

pub open spec fn count_match_at_pos(nums: Seq<i32>, j: int, p: int, d: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        count_match_at_pos(nums, j - 1, p, d) + (if digit_at(nums[j - 1] as int, p) == d { 1int } else { 0int })
    }
}

proof fn lemma_count_diff_via_match(nums: Seq<i32>, i: int, j: int, p: int)
    requires 0 <= j <= i < nums.len(),
    ensures count_diff_at_pos(nums, i, j, p) == j - count_match_at_pos(nums, j, p, digit_at(nums[i] as int, p)),
    decreases j,
{
    if j > 0 {
        lemma_count_diff_via_match(nums, i, j - 1, p);
    }
}

proof fn lemma_count_match_bound(nums: Seq<i32>, j: int, p: int, d: int)
    requires 0 <= j,
    ensures 0 <= count_match_at_pos(nums, j, p, d) <= j,
    decreases j,
{
    if j > 0 {
        lemma_count_match_bound(nums, j - 1, p, d);
    }
}

pub open spec fn best_from_prefix_at_pos(nums: Seq<i32>, i: int, p: int) -> int {
    i - count_match_at_pos(nums, i, p, digit_at(nums[i] as int, p))
}

proof fn lemma_pair_sum_for_i_via_prefix(nums: Seq<i32>, i: int)
    requires 0 <= i < nums.len(),
    ensures Solution::pair_sum_for_i(nums, i, i) ==
        best_from_prefix_at_pos(nums, i, 0) + best_from_prefix_at_pos(nums, i, 1) + best_from_prefix_at_pos(nums, i, 2)
        + best_from_prefix_at_pos(nums, i, 3) + best_from_prefix_at_pos(nums, i, 4) + best_from_prefix_at_pos(nums, i, 5)
        + best_from_prefix_at_pos(nums, i, 6) + best_from_prefix_at_pos(nums, i, 7) + best_from_prefix_at_pos(nums, i, 8),
{
    lemma_pair_sum_decompose(nums, i, i);
    assert forall |p: int| 0 <= p < 9 implies
        #[trigger] count_diff_at_pos(nums, i, i, p) == best_from_prefix_at_pos(nums, i, p) by {
        lemma_count_diff_via_match(nums, i, i, p);
    }
}

fn digit_at_exec(n: i32, p: usize) -> (res: usize)
    requires 0 <= n < 1_000_000_000, p <= 8,
    ensures res as int == digit_at(n as int, p as int), res < 10,
    decreases p,
{
    if p == 0 {
        (n % 10) as usize
    } else {
        digit_at_exec(n / 10, p - 1)
    }
}

impl Solution {
    pub fn sum_digit_differences(nums: Vec<i32>) -> (result: i64)
        requires
            2 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000,
            forall |i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len()
                ==> Self::digit_count(#[trigger] nums[i] as int) == Self::digit_count(#[trigger] nums[j] as int),
        ensures
            Self::sum_digit_differences_spec(nums@, result as int),
    {
        let n = nums.len();
        let mut cnt: Vec<Vec<i64>> = Vec::new();
        let mut pi: usize = 0;
        while pi < 9
            invariant
                pi <= 9,
                cnt.len() == pi,
                forall |p: int| 0 <= p < pi ==> #[trigger] cnt[p].len() == 10,
                forall |p: int, d: int| 0 <= p < pi && 0 <= d < 10 ==> #[trigger] cnt[p][d] == 0,
            decreases 9 - pi,
        {
            let mut drow: Vec<i64> = Vec::new();
            let mut di: usize = 0;
            while di < 10
                invariant di <= 10, drow.len() == di, forall |d: int| 0 <= d < di ==> #[trigger] drow[d] == 0,
                decreases 10 - di,
            {
                drow.push(0);
                di += 1;
            }
            assert(drow.len() == 10);
            assert(forall |d: int| 0 <= d < 10 ==> #[trigger] drow[d] == 0);
            let ghost drow_ghost = drow@;
            let ghost old_pi = pi as int;
            cnt.push(drow);
            proof {
                assert(cnt@[old_pi]@ =~= drow_ghost);
                assert(cnt@[old_pi]@.len() == 10);
                assert forall |p: int| 0 <= p < old_pi + 1 implies cnt[p].len() == 10 by {}
                assert forall |p: int, d: int| 0 <= p < old_pi + 1 && 0 <= d < 10 implies
                    #[trigger] cnt[p][d] == 0 by {}
            }
            pi += 1;
        }

        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                n <= 100000,
                cnt.len() == 9,
                forall |p: int| 0 <= p < 9 ==> #[trigger] cnt[p].len() == 10,
                forall |i2: int| 0 <= i2 < n ==> 1 <= #[trigger] nums@[i2] < 1_000_000_000,
                i <= n,
                forall |p: int, d: int| 0 <= p < 9 && 0 <= d < 10 ==>
                    #[trigger] cnt[p][d] as int == count_match_at_pos(nums@, i as int, p, d),
                total as int == Solution::all_pair_sum(nums@, i as int),
                0 <= total,
            decreases n - i,
        {
            let x = nums[i];
            let mut contrib: i64 = 0;
            let mut p: usize = 0;
            while p < 9
                invariant
                    n == nums.len(),
                    n <= 100000,
                    i < n,
                    x == nums[i as int],
                    0 <= x < 1_000_000_000,
                    cnt.len() == 9,
                    forall |pp: int| 0 <= pp < 9 ==> #[trigger] cnt[pp].len() == 10,
                    p <= 9,
                    forall |pp: int, d: int| 0 <= pp < 9 && 0 <= d < 10 ==>
                        #[trigger] cnt[pp][d] as int == count_match_at_pos(nums@, i as int, pp, d),
                    contrib as int == (
                        if p >= 1 { best_from_prefix_at_pos(nums@, i as int, 0) } else { 0int }
                    ) + (if p >= 2 { best_from_prefix_at_pos(nums@, i as int, 1) } else { 0int })
                        + (if p >= 3 { best_from_prefix_at_pos(nums@, i as int, 2) } else { 0int })
                        + (if p >= 4 { best_from_prefix_at_pos(nums@, i as int, 3) } else { 0int })
                        + (if p >= 5 { best_from_prefix_at_pos(nums@, i as int, 4) } else { 0int })
                        + (if p >= 6 { best_from_prefix_at_pos(nums@, i as int, 5) } else { 0int })
                        + (if p >= 7 { best_from_prefix_at_pos(nums@, i as int, 6) } else { 0int })
                        + (if p >= 8 { best_from_prefix_at_pos(nums@, i as int, 7) } else { 0int })
                        + (if p >= 9 { best_from_prefix_at_pos(nums@, i as int, 8) } else { 0int }),
                    0 <= contrib,
                    contrib <= (p as i64) * 100000,
                decreases 9 - p,
            {
                let d = digit_at_exec(x, p);
                assert(d < 10);
                assert(p < cnt.len());
                assert(d < cnt[p as int].len());
                assert(d as int == digit_at(nums@[i as int] as int, p as int));
                let matching = cnt[p][d];
                assert(matching as int == count_match_at_pos(nums@, i as int, p as int, d as int));
                proof {
                    lemma_count_match_bound(nums@, i as int, p as int, d as int);
                }
                assert(count_match_at_pos(nums@, i as int, p as int, d as int) <= i as int);
                assert(matching as int <= i as int);
                assert((i as i64) as int == i as int);
                assert(matching <= i as i64);
                let term = (i as i64) - matching;
                assert(term as int == best_from_prefix_at_pos(nums@, i as int, p as int));
                assert(0 <= term);
                assert(term <= 100000);
                assert(0 <= contrib);
                assert(contrib <= (p as i64) * 100000);
                assert(((p + 1) as i64) == (p as i64) + 1);
                assert(contrib + term <= ((p as i64) + 1) * 100000) by (nonlinear_arith)
                    requires contrib <= (p as i64) * 100000, term <= 100000;
                assert(contrib + term <= ((p + 1) as i64) * 100000);
                contrib = contrib + term;
                p += 1;
            }
            proof {
                lemma_pair_sum_for_i_via_prefix(nums@, i as int);
                assert(contrib as int == Solution::pair_sum_for_i(nums@, i as int, i as int));
            }

            let mut p2: usize = 0;
            while p2 < 9
                invariant
                    n == nums.len(),
                    n <= 100000,
                    i < n,
                    x == nums[i as int],
                    0 <= x < 1_000_000_000,
                    cnt.len() == 9,
                    forall |pp: int| 0 <= pp < 9 ==> #[trigger] cnt[pp].len() == 10,
                    p2 <= 9,
                    forall |pp: int, d: int| p2 <= pp < 9 && 0 <= d < 10 ==>
                        #[trigger] cnt[pp][d] as int == count_match_at_pos(nums@, i as int, pp, d),
                    forall |pp: int, d: int| 0 <= pp < p2 && 0 <= d < 10 ==>
                        #[trigger] cnt[pp][d] as int == count_match_at_pos(nums@, i as int + 1, pp, d),
                decreases 9 - p2,
            {
                let d2 = digit_at_exec(x, p2);
                assert(d2 < 10);
                assert(p2 < cnt.len());
                assert(d2 < cnt[p2 as int].len());
                assert(d2 as int == digit_at(nums@[i as int] as int, p2 as int));
                let old_val = cnt[p2][d2];
                assert(old_val as int == count_match_at_pos(nums@, i as int, p2 as int, d2 as int));
                proof {
                    lemma_count_match_bound(nums@, i as int, p2 as int, d2 as int);
                }
                assert(count_match_at_pos(nums@, i as int, p2 as int, d2 as int) <= i as int);
                assert(old_val as int <= i as int);
                assert((i as i64) as int == i as int);
                assert(old_val <= i as i64);
                assert(count_match_at_pos(nums@, i as int + 1, p2 as int, d2 as int)
                    == count_match_at_pos(nums@, i as int, p2 as int, d2 as int) + 1);
                assert forall |d: int| 0 <= d < 10 && d != d2 as int implies
                    count_match_at_pos(nums@, i as int + 1, p2 as int, d)
                        == #[trigger] count_match_at_pos(nums@, i as int, p2 as int, d) by {}
                let mut row = cnt[p2].clone();
                row.set(d2, old_val + 1);
                cnt.set(p2, row);
                p2 += 1;
            }

            proof {
                Solution::lemma_all_pair_sum_bound(nums@, i as int);
                Solution::lemma_pair_sum_for_i_bound(nums@, i as int, i as int);
                assert(total as int <= 90_000_000_000int);
                assert(contrib as int <= 9 * (i as int));
                assert(i as int <= 100000int);
                assert(contrib as int <= 900000int) by (nonlinear_arith)
                    requires contrib as int <= 9 * (i as int), (i as int) <= 100000int;
                assert(total as int + contrib as int <= 90_000_000_000int + 900000int);
            }
            total = total + contrib;
            proof {
                assert(Solution::all_pair_sum(nums@, i as int + 1)
                    == Solution::all_pair_sum(nums@, i as int) + Solution::pair_sum_for_i(nums@, i as int, i as int));
            }
            i += 1;
        }

        total
    }
}

}
