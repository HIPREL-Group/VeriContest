use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn fits_oriented(w1: i32, h1: i32, w2: i32, h2: i32, a: i32, b: i32) -> bool {
    (w1 + w2 <= a && h1 <= b && h2 <= b) ||
    (h1 + h2 <= b && w1 <= a && w2 <= a)
}

pub open spec fn fits(x1: i32, y1: i32, x2: i32, y2: i32, a: i32, b: i32) -> bool {
    fits_oriented(x1, y1, x2, y2, a, b) ||
    fits_oriented(y1, x1, x2, y2, a, b) ||
    fits_oriented(x1, y1, y2, x2, a, b) ||
    fits_oriented(y1, x1, y2, x2, a, b)
}

pub open spec fn is_valid_pair(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i: int, j: int) -> bool {
    0 <= i && i < x.len() && 0 <= j && j < x.len() && i != j &&
    fits(x[i], y[i], x[j], y[j], a, b)
}

pub open spec fn area(x: Seq<i32>, y: Seq<i32>, i: int, j: int) -> i32 {
    (x[i] as int * y[i] as int + x[j] as int * y[j] as int) as i32
}

pub open spec fn is_correct_ans(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, ans: i32) -> bool {
    (forall|i: int, j: int| #[trigger] is_valid_pair(x, y, a, b, i, j) ==> area(x, y, i, j) <= ans)
    &&
    (
        (ans == 0 && (forall|i: int, j: int| !is_valid_pair(x, y, a, b, i, j)))
        ||
        (exists|i: int, j: int| #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
    )
}

pub open spec fn ans_is_upper_bound(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32) -> bool {
    forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) ==> area(x, y, i, j) <= ans
}

pub open spec fn ans_witness_exists(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32) -> bool {
    (ans == 0 && (forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() ==> !#[trigger] is_valid_pair(x, y, a, b, i, j)))
    ||
    (exists|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
}

pub open spec fn inner_ans_is_upper_bound(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, j_bound: int, ans: i32) -> bool {
    ans_is_upper_bound(x, y, a, b, i_bound, ans) &&
    (forall|j: int| i_bound < j && j < j_bound ==> 
        (#[trigger] is_valid_pair(x, y, a, b, i_bound, j) ==> area(x, y, i_bound, j) <= ans))
}

pub open spec fn inner_ans_witness_exists(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, j_bound: int, ans: i32) -> bool {
    (ans == 0 && 
        (forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() ==> !#[trigger] is_valid_pair(x, y, a, b, i, j)) &&
        (forall|j: int| i_bound < j && j < j_bound ==> !#[trigger] is_valid_pair(x, y, a, b, i_bound, j)))
    ||
    (exists|i: int, j: int| 
        ((0 <= i && i < i_bound && i < j && j < x.len()) || (i == i_bound && i_bound < j && j < j_bound)) &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
}

pub struct Solution;

impl Solution {
    pub fn fits_oriented(w1: i32, h1: i32, w2: i32, h2: i32, a: i32, b: i32) -> (res: bool)
        requires 0 <= w1 && w1 <= 100, 0 <= h1 && h1 <= 100, 0 <= w2 && w2 <= 100, 0 <= h2 && h2 <= 100
        ensures res == crate::fits_oriented(w1, h1, w2, h2, a, b)
    {
        (w1 + w2 <= a && h1 <= b && h2 <= b) ||
        (h1 + h2 <= b && w1 <= a && w2 <= a)
    }

    pub fn fits(x1: i32, y1: i32, x2: i32, y2: i32, a: i32, b: i32) -> (res: bool)
        requires 0 <= x1 && x1 <= 100, 0 <= y1 && y1 <= 100, 0 <= x2 && x2 <= 100, 0 <= y2 && y2 <= 100
        ensures res == crate::fits(x1, y1, x2, y2, a, b)
    {
        Solution::fits_oriented(x1, y1, x2, y2, a, b) ||
        Solution::fits_oriented(y1, x1, x2, y2, a, b) ||
        Solution::fits_oriented(x1, y1, y2, x2, a, b) ||
        Solution::fits_oriented(y1, x1, y2, x2, a, b)
    }

    pub fn two_seals(n: usize, a: i32, b: i32, x: Vec<i32>, y: Vec<i32>) -> (ans: i32)
        requires
            n == x.len(),
            n == y.len(),
            1 <= n && n <= 100,
            1 <= a && a <= 100,
            1 <= b && b <= 100,
            forall|i: int| 0 <= i && i < n ==> 1 <= x@[i] && x@[i] <= 100,
            forall|i: int| 0 <= i && i < n ==> 1 <= y@[i] && y@[i] <= 100,
        ensures
            is_correct_ans(x@, y@, a, b, ans),
    {
        let mut ans: i32 = 0;
        let mut i = 0;
        while i < n {
            let mut j = i + 1;
            while j < n {
                let is_fit = Solution::fits(x[i], y[i], x[j], y[j], a, b);
                if is_fit {
                    let xi = x[i]; let yi = y[i]; let xj = x[j]; let yj = y[j];
                    let area_val: i32 = xi * yi + xj * yj;
                    if area_val > ans {
                        ans = area_val;
                    }
                }
                j += 1;
            }
            i += 1;
        }
        ans
    }
}

}
