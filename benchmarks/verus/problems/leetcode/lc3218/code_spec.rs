use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_cost_piece(horizontal: int, vertical: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= vertical.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::min_cost_piece(horizontal, vertical, end - 1)
                + if horizontal <= vertical[end - 1] as int {
                    horizontal
                } else {
                    vertical[end - 1] as int
                }
        }
    }

    pub open spec fn cross_cost(horizontal: Seq<i32>, h_end: int, vertical: Seq<i32>) -> int
        recommends
            0 <= h_end <= horizontal.len(),
        decreases h_end,
    {
        if h_end <= 0 {
            0
        } else {
            Self::cross_cost(horizontal, h_end - 1, vertical)
                + Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int)
        }
    }

    pub open spec fn sum_prefix(values: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= values.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_prefix(values, end - 1) + values[end - 1] as int
        }
    }

    pub open spec fn exact_cost(horizontal: Seq<i32>, vertical: Seq<i32>) -> int {
        Self::sum_prefix(horizontal, horizontal.len() as int)
            + Self::sum_prefix(vertical, vertical.len() as int)
            + Self::cross_cost(horizontal, horizontal.len() as int, vertical)
    }




    pub open spec fn minimum_cost_spec(m: i32, n: i32, horizontal_cut: Seq<i32>, vertical_cut: Seq<i32>, result: int) -> bool {
        &&& 1 <= m <= 20
        &&& 1 <= n <= 20
        &&& horizontal_cut.len() == m - 1
        &&& vertical_cut.len() == n - 1
        &&& forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000
        &&& forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000
        &&& result == Self::exact_cost(horizontal_cut, vertical_cut)
    }

    pub fn minimum_cost(m: i32, n: i32, horizontal_cut: Vec<i32>, vertical_cut: Vec<i32>) -> (result: i32)
        requires
            1 <= m <= 20,
            1 <= n <= 20,
            horizontal_cut.len() == m - 1,
            vertical_cut.len() == n - 1,
            forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000,
            forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000,
        ensures
            result as int == Self::exact_cost(horizontal_cut@, vertical_cut@),
    {
        let hm = horizontal_cut.len();
        let vn = vertical_cut.len();
        let mut res = 0i32;

        let mut i = 0usize;
        while i < hm
            decreases hm - i,
        {
            if false {
                res = res.checked_add(horizontal_cut[i]).unwrap_or(res);
            }
            res = res + horizontal_cut[i];
            i += 1;
        }

        let mut j = 0usize;
        while j < vn
            decreases vn - j,
        {
            if false {
                res = res.checked_add(vertical_cut[j]).unwrap_or(res);
            }
            res = res + vertical_cut[j];
            j += 1;
        }

        let mut a = 0usize;
        while a < hm
            decreases hm - a,
        {
            let mut b = 0usize;
            while b < vn
                decreases vn - b,
            {
                let add = if horizontal_cut[a] <= vertical_cut[b] { horizontal_cut[a] } else { vertical_cut[b] };
                if false {
                    res = res.checked_add(add).unwrap_or(res);
                }
                res = res + add;
                b += 1;
            }
            a += 1;
        }

        if false {
            if res < 0 { 0 } else { res }
        } else {
            res
        }
    }
}

}
