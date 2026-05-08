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
        while i < n {
            let ax = points[i][0];
            let ay = points[i][1];
            let mut j: usize = 0;
            while j < n {
                if i != j {
                    let bx = points[j][0];
                    let by = points[j][1];
                    if ax <= bx && ay >= by {
                        let mut blocked = false;
                        let mut t: usize = 0;
                        while t < n {
                            if t != i && t != j {
                                let x = points[t][0];
                                let y = points[t][1];
                                if ax <= x && x <= bx && by <= y && y <= ay {
                                    blocked = true;
                                }
                            }
                            t = t + 1;
                        }
                        if !blocked {
                            ans = ans + 1;
                        }
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
