use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn check_no_divisor(n: int, d: int) -> bool {
        n % d != 0
    }

    pub open spec fn prime_int(n: int) -> bool {
        n > 1 && forall|d: int| 2 <= d && d * d <= n ==> #[trigger] Self::check_no_divisor(n, d)
    }

    pub open spec fn is_candidate_prime(n: int) -> bool {
        n > 10 && Self::prime_int(n)
    }

    pub open spec fn row_delta(d: int) -> int {
        if d == 0 {
            0
        } else if d == 1 {
            1
        } else if d == 2 {
            1
        } else if d == 3 {
            1
        } else if d == 4 {
            0
        } else if d == 5 {
            -1
        } else if d == 6 {
            -1
        } else {
            -1
        }
    }

    pub open spec fn col_delta(d: int) -> int {
        if d == 0 {
            1
        } else if d == 1 {
            1
        } else if d == 2 {
            0
        } else if d == 3 {
            -1
        } else if d == 4 {
            -1
        } else if d == 5 {
            -1
        } else if d == 6 {
            0
        } else {
            1
        }
    }

    pub open spec fn row_at(r: int, d: int, step: int) -> int {
        r + step * Self::row_delta(d)
    }

    pub open spec fn col_at(c: int, d: int, step: int) -> int {
        c + step * Self::col_delta(d)
    }

    pub open spec fn in_bounds(mat: Seq<Vec<i32>>, rr: int, cc: int) -> bool {
        mat.len() > 0 && 0 <= rr < mat.len() && 0 <= cc < mat[0].len() as int
    }

    pub open spec fn path_valid(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step: int) -> bool {
        0 <= step <= 5 && mat.len() > 0 && forall|t: int| 0 <= t <= step ==> Self::in_bounds(mat, Self::row_at(r, d, t), Self::col_at(c, d, t))
    }

    pub open spec fn number_on_path(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step: int) -> int
        decreases step
    {
        if step <= 0 {
            mat[r][c] as int
        } else {
            Self::number_on_path(mat, r, c, d, step - 1) * 10 + mat[Self::row_at(r, d, step)][Self::col_at(c, d, step)] as int
        }
    }

    pub open spec fn direction_numbers_upto(mat: Seq<Vec<i32>>, r: int, c: int, d: int, step_bound: int) -> Seq<i32>
        decreases step_bound
    {
        if step_bound <= 0 {
            seq![]
        } else {
            let prev = Self::direction_numbers_upto(mat, r, c, d, step_bound - 1);
            if Self::path_valid(mat, r, c, d, step_bound) {
                prev.push(Self::number_on_path(mat, r, c, d, step_bound) as i32)
            } else {
                prev
            }
        }
    }

    pub open spec fn cell_numbers_upto(mat: Seq<Vec<i32>>, r: int, c: int, d_bound: int) -> Seq<i32>
        decreases d_bound
    {
        if d_bound <= 0 {
            seq![]
        } else {
            Self::cell_numbers_upto(mat, r, c, d_bound - 1) + Self::direction_numbers_upto(mat, r, c, d_bound - 1, 5)
        }
    }

    pub open spec fn all_numbers_upto(mat: Seq<Vec<i32>>, idx_bound: int) -> Seq<i32>
        decreases idx_bound
    {
        if idx_bound <= 0 || mat.len() == 0 || mat[0].len() == 0 {
            seq![]
        } else {
            let prev = Self::all_numbers_upto(mat, idx_bound - 1);
            let idx = idx_bound - 1;
            if 0 <= idx < (mat.len() * mat[0].len()) as int {
                prev + Self::cell_numbers_upto(mat, idx / (mat[0].len() as int), idx % (mat[0].len() as int), 8)
            } else {
                prev
            }
        }
    }

    pub open spec fn all_numbers(mat: Seq<Vec<i32>>) -> Seq<i32> {
        if mat.len() == 0 || mat[0].len() == 0 {
            seq![]
        } else {
            Self::all_numbers_upto(mat, (mat.len() * mat[0].len()) as int)
        }
    }

    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    pub fn most_frequent_prime(mat: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= mat.len() <= 6,
            forall|i: int| 0 <= i < mat.len() ==> 1 <= #[trigger] mat[i].len() <= 6,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[0].len() ==> 1 <= #[trigger] mat[i][j] <= 9,
        ensures
            ((res == -1) && (forall|k: int| 0 <= k < Self::all_numbers(mat@).len() ==> !Self::is_candidate_prime(#[trigger] Self::all_numbers(mat@)[k] as int))) ||
            (Self::is_candidate_prime(res as int) &&
             forall|k: int| 0 <= k < Self::all_numbers(mat@).len() && Self::is_candidate_prime(#[trigger] Self::all_numbers(mat@)[k] as int) ==>
                 (Self::count_occurrences(Self::all_numbers(mat@), Self::all_numbers(mat@)[k]) < Self::count_occurrences(Self::all_numbers(mat@), res) ||
                  (Self::count_occurrences(Self::all_numbers(mat@), Self::all_numbers(mat@)[k]) == Self::count_occurrences(Self::all_numbers(mat@), res) && Self::all_numbers(mat@)[k] <= res))),
    {
    }
}

}
