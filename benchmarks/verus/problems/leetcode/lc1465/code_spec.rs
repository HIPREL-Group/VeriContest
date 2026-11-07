use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn max_adj_diff(sorted: Seq<i32>, bound: int) -> int
        decreases sorted.len(),
    {
        if sorted.len() == 0 {
            bound
        } else {
            Self::spec_max(
                bound - sorted[sorted.len() - 1] as int,
                Self::max_adj_diff(sorted.drop_last(), sorted[sorted.len() - 1] as int)
            )
        }
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort(input: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted(result@),
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    fn find_max_gap(cuts: &Vec<i32>, bound: i32) -> (result: i32)
        requires
            1 <= cuts.len() <= 100_000,
            bound >= 2,
            forall |k: int| 0 <= k < cuts.len() ==> 1 <= #[trigger] cuts[k] < bound,
            forall |k: int, m: int| 0 <= k < m < cuts.len() ==> cuts[k] != cuts[m],
        ensures
            1 <= result < bound,
            exists |sorted: Seq<i32>|
                Self::is_sorted(sorted)
                && Self::is_perm(sorted, cuts@)
                && result as int == Self::max_adj_diff(sorted, bound as int),
    {
        let sorted = Self::ms_sort(cuts);
        let n = sorted.len();
        let mut max_g: i32 = sorted[0];
        let mut i: usize = 1;
        while i < n
        {
            let gap = sorted[i] - sorted[i - 1];
            if gap > max_g {
                max_g = gap;
            }
            i = i + 1;
        }
        let last_gap = bound - sorted[n - 1];
        if last_gap > max_g {
            max_g = last_gap;
        }
        max_g
    }

    pub fn max_area(h: i32, w: i32, horizontal_cuts: Vec<i32>, vertical_cuts: Vec<i32>) -> (result: i32)
        requires
            2 <= h <= 1_000_000_000,
            2 <= w <= 1_000_000_000,
            1 <= horizontal_cuts.len() <= 100_000,
            1 <= vertical_cuts.len() <= 100_000,
            forall |i: int| 0 <= i < horizontal_cuts.len() ==> 1 <= #[trigger] horizontal_cuts[i] < h,
            forall |j: int| 0 <= j < vertical_cuts.len() ==> 1 <= #[trigger] vertical_cuts[j] < w,
            forall |i: int, j: int| 0 <= i < j < horizontal_cuts.len() ==> horizontal_cuts[i] != horizontal_cuts[j],
            forall |i: int, j: int| 0 <= i < j < vertical_cuts.len() ==> vertical_cuts[i] != vertical_cuts[j],
        ensures
            0 <= result < 1_000_000_007,
            exists |sh: Seq<i32>, sv: Seq<i32>|
                Self::is_sorted(sh)
                && Self::is_perm(sh, horizontal_cuts@)
                && Self::is_sorted(sv)
                && Self::is_perm(sv, vertical_cuts@)
                && result as int == (Self::max_adj_diff(sh, h as int) * Self::max_adj_diff(sv, w as int)) % 1_000_000_007,
    {
        let max_h = Self::find_max_gap(&horizontal_cuts, h);
        let max_v = Self::find_max_gap(&vertical_cuts, w);
        ((max_h as i64 * max_v as i64) % 1_000_000_007i64) as i32
    }
}

}
