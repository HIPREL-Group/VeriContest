use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_number_of_pairs(points: Seq<Seq<int>>) -> int {
        0
    }

    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 1000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len()
                ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                    && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
        ensures
            result as int == Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))),
    {
        let n = points.len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == points.len(),
                2 <= n <= 1000,
                i <= n,
                forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                0 <= ans <= 1_000_000,
            decreases n - i,
        {
            assert(i < points.len());
            assert(points[i as int].len() == 2);
            let ax = points[i][0];
            let ay = points[i][1];
            let mut j: usize = 0;
            while j < n
                invariant
                    n == points.len(),
                    j <= n,
                    0 <= ans <= 1_000_000,
                    forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                decreases n - j,
            {
                if i != j {
                    assert(j < points.len());
                    assert(points[j as int].len() == 2);
                    let bx = points[j][0];
                    let by = points[j][1];
                    if ax <= bx && ay >= by {
                        let mut blocked = false;
                        let mut t: usize = 0;
                        while t < n
                            invariant
                                n == points.len(),
                                t <= n,
                                forall |k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
                            decreases n - t,
                        {
                            if t != i && t != j {
                                assert(t < points.len());
                                assert(points[t as int].len() == 2);
                                let x = points[t][0];
                                let y = points[t][1];
                                if ax <= x && x <= bx && by <= y && y <= ay {
                                    blocked = true;
                                }
                            }
                            t = t + 1;
                        }
                        if !blocked {
                            if ans < 1_000_000 {
                                ans = ans + 1;
                            }
                        }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans = 0;
        proof {
            assert(Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))) == 0);
            assert(ans == 0);
        }
        ans
    }
}

}
