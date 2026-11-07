use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn x_at(x: Seq<i64>, j: int) -> int {
        x[j] as int
    }

    pub open spec fn middle_felled(x: Seq<i64>, h: Seq<i64>, i: int, last: int) -> int
        recommends
            x.len() == h.len(),
            1 <= x.len(),
            1 <= i < x.len(),
        decreases x.len() as int - i,
    {
        let n = x.len() as int;
        if i >= n - 1 {
            0
        } else if Self::x_at(x, i) > last + Self::x_at(h, i) {
            1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
        } else if Self::x_at(x, i) + Self::x_at(h, i) < Self::x_at(x, i + 1) {
            1 + Self::middle_felled(x, h, i + 1, Self::x_at(x, i) + Self::x_at(h, i))
        } else {
            Self::middle_felled(x, h, i + 1, Self::x_at(x, i))
        }
    }

    pub open spec fn woodcutters_answer(x: Seq<i64>, h: Seq<i64>) -> int {
        if x.len() <= 1 {
            x.len() as int
        } else {
            2 + Self::middle_felled(x, h, 1, Self::x_at(x, 0))
        }
    }

    pub fn max_felled_trees(x: Vec<i64>, h: Vec<i64>) -> (result: i64)
        requires
            x.len() == h.len(),
            1 <= x.len() <= 100_000,
            forall |j: int| 0 <= j < x.len() ==> 1 <= #[trigger] x@[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < h.len() ==> 1 <= #[trigger] h@[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < x.len() - 1 ==> x@[j] < #[trigger] x@[j + 1],
        ensures
            result as int == Self::woodcutters_answer(x@, h@),
    {
        let n = x.len();
        if n == 1 {
            return 1i64;
        }
        let mut ans: i64 = 2;
        let mut last: i64 = x[0];
        let mut i: usize = 1;
        while i < n - 1 {
            let xi = x[i];
            let hi = h[i];
            if xi > last + hi {
                ans = ans + 1;
                last = xi;
            } else if xi + hi < x[i + 1] {
                ans = ans + 1;
                last = xi + hi;
            } else {
                last = xi;
            }
            i = i + 1;
        }
        ans
    }
}

}
