use vstd::prelude::*;

fn main() {}

verus! {
pub struct Solution;

impl Solution {
    pub fn max_distance(colors: Vec<i32>) -> (result: i32)
        requires
            2 <= colors.len() <= 100,
            forall |i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 100,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j],
        ensures
            result >= 0,
            exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j] && #[trigger] (j - i) == result,
            forall |i: int, j: int| 0 <= i < j < colors.len() ==> colors[i] == colors[j] || #[trigger] (j - i) <= result,
    {
        let n = colors.len();
        let mut result: i32 = 0;
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 1;
        let mut i = 0;
        while i < n
            invariant
                2 <= n <= 100,
                n == colors.len(),
                0 <= i <= n,
                result >= 0,
                0 <= best_i < n,
                0 < best_j < n,
                best_i < best_j,
                result == 0 || (colors[best_i] != colors[best_j] && (best_j - best_i) == result),
                forall |ii: int, jj: int| 0 <= ii < i && ii < jj < n ==> colors[ii] == colors[jj] || #[trigger] (jj - ii) <= result,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] colors[k] <= 100
            decreases n - i
        {
            let mut j = n - 1;
            while j > i
                invariant
                    2 <= n <= 100,
                    0 <= i < n,
                    n == colors.len(),
                    i <= j <= n - 1,
                    result >= 0,
                    0 <= best_i < n,
                    0 < best_j < n,
                    best_i < best_j,
                    result == 0 || (colors[best_i] != colors[best_j] && (best_j - best_i) == result),
                    forall |ii: int, jj: int| 0 <= ii < i && ii < jj < n ==> colors[ii] == colors[jj] || #[trigger] (jj - ii) <= result,
                    forall |jj: int| j < jj < n ==> colors[i as int] == colors[jj] || #[trigger] (jj - i) <= result,
                    forall |k: int| 0 <= k < n ==> 0 <= #[trigger] colors[k] <= 100
                decreases j - i
            {
                let dist = (j - i) as i32;
                if colors[i] != colors[j] && dist > result {
                    result = dist;
                    proof {
                        best_i = i as int;
                        best_j = j as int;
                    }
                }
                j -= 1;
            }
            i += 1;
        }
        proof {
            assert(result > 0) by {
                let ei = choose |ii: int| exists |jj: int| 0 <= ii && ii < jj && jj < n && #[trigger] colors[ii] != #[trigger] colors[jj];
                let ej = choose |jj: int| 0 <= ei && ei < jj && jj < n && #[trigger] colors[ei] != #[trigger] colors[jj];
                assert(0 <= ei < ej < n);
                assert(colors[ei] != colors[ej]);
                assert(colors[ei] == colors[ej] || (ej - ei) <= result);
            };
        }
        result
    }
}
}
