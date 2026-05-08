use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_independent(t: Seq<i32>) -> bool {
        forall|k: int|
            0 <= k < t.len() - 1 ==> !(#[trigger] t[k] == 1 && t[k + 1] == 1)
    }

    pub open spec fn spec_maximal_independent(t: Seq<i32>) -> bool {
        Self::spec_independent(t) && (forall|k: int|
            0 <= k < t.len() ==> (#[trigger] t[k] == 1 || (k > 0 && t[k - 1] == 1)
                || (k + 1 < t.len() && t[k + 1] == 1)))
    }

    pub open spec fn spec_extends(initial: Seq<i32>, t: Seq<i32>) -> bool {
        initial.len() == t.len() && (forall|k: int|
            0 <= k < initial.len() ==> (#[trigger] initial[k] == 1 ==> t[k] == 1))
    }

    pub open spec fn spec_sum_ones_helper(s: Seq<i32>, i: int) -> int
        decreases s.len() - i,
    {
        if i >= s.len() {
            0int
        } else {
            (if s[i] == 1 {
                1int
            } else {
                0int
            }) + Self::spec_sum_ones_helper(s, i + 1)
        }
    }

    pub open spec fn spec_sum_ones(s: Seq<i32>) -> int {
        Self::spec_sum_ones_helper(s, 0)
    }

    pub open spec fn spec_run_end(s: Seq<i32>, i: int) -> int
        recommends
            0 <= i < s.len(),
            s[i] == 0,
        decreases s.len() - i,
    {
        if i + 1 < s.len() && s[i + 1] == 0 {
            Self::spec_run_end(s, i + 1)
        } else {
            i + 1
        }
    }

    pub open spec fn spec_run_extra(l: int, left: bool, right: bool) -> int {
        if left && right {
            l / 3
        } else if left || right {
            (l + 1) / 3
        } else {
            (l + 2) / 3
        }
    }

    pub open spec fn spec_addon_from_index(s: Seq<i32>, i: int) -> int
        recommends
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        decreases s.len() - i,
    {
        if i < 0 {
            0int
        } else if i >= s.len() {
            0int
        } else {
            if s[i] == 1 {
                Self::spec_addon_from_index(s, i + 1)
            } else if s[i] == 0 {
                let j = Self::spec_run_end(s, i);
                let l = j - i;
                let left = i > 0 && s[i - 1] == 1;
                let right = if j < s.len() {
                    s[j] == 1
                } else {
                    false
                };
                Self::spec_run_extra(l, left, right) + Self::spec_addon_from_index(s, j)
            } else {
                0int
            }
        }
    }

    pub open spec fn spec_closed_form_total(s: Seq<i32>) -> int {
        Self::spec_sum_ones(s) + Self::spec_addon_from_index(s, 0)
    }

    fn zero_run_end(s: &Vec<i32>, i: usize) -> (j_end: usize)
        requires
            i < s.len(),
            s@[i as int] == 0,
            forall|k: int|
                0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
        ensures
            j_end as int == Self::spec_run_end(s@, i as int),
            i < j_end <= s.len(),
            forall|k: int|
                i <= k < j_end as int ==> #[trigger] s@[k] == 0,
            j_end as int == s.len() as int || s@[j_end as int] == 1,
        decreases s.len() - i,
    {
        let n = s.len();
        if i + 1 >= n {
            let j_end = i + 1;
            j_end
        } else {
            if s[i + 1] != 0 {
                let j_end = i + 1;
                j_end
            } else {
                Self::zero_run_end(s, i + 1)
            }
        }
    }

    pub fn min_total_seated_students(s: &Vec<i32>) -> (res: i64)
        requires
            1 <= s.len() <= 200_000,
            forall|k: int|
                0 <= k < s.len() as int ==> #[trigger] s[k] == 0 || s[k] == 1,
            forall|k: int|
                0 <= k < s.len() as int - 1 ==> !(#[trigger] s[k] == 1 && s[k + 1] == 1),
        ensures
            res as int == Self::spec_closed_form_total(s@),
    {
        let n = s.len();
        let mut ones: i64 = 0;
        let mut add: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            if s[i] == 1 {
                ones = ones + 1;
                i = i + 1;
            } else {
                let j_end = Self::zero_run_end(s, i);
                let l: usize = j_end - i;
                let left: bool = if i > 0 {
                    s[i - 1] == 1
                } else {
                    false
                };
                let right: bool = if j_end < n {
                    s[j_end] == 1
                } else {
                    false
                };
                let extra: i64 = if left && right {
                    (l as i64) / 3
                } else if left || right {
                    ((l as i64) + 1) / 3
                } else {
                    ((l as i64) + 2) / 3
                };
                add = add + extra;
                i = j_end;
            }
        }
        ones + add
    }
}

}
