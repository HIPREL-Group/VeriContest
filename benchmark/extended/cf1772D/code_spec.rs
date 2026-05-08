use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_int(v: int) -> int {
        if v >= 0 { v } else { -v }
    }

    pub open spec fn valid_x(a: Seq<i32>, x: int) -> bool {
        forall|i: int| 0 <= i && i + 1 < a.len() ==> #[trigger] Self::abs_int(a[i] as int - x) <= Self::abs_int(a[i + 1] as int - x)
    }

    pub fn absolute_sorting(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 200000,
            forall|i: int| 0 <= i < a.len() as int ==> 0 <= #[trigger] a[i] <= 1000000000,
        ensures
            (res == -1) || (0 <= res <= 1000000000 && Self::valid_x(a@, res as int)),
    {
        let n = a.len();
        let mut low: i64 = 0;
        let mut high: i64 = 1000000000;
        let mut i: usize = 0;
        while i + 1 < n {
            let x = a[i] as i64;
            let y = a[i + 1] as i64;
            if x < y {
                let ub = (x + y) / 2;
                if ub < high {
                    high = ub;
                }
            } else if x > y {
                let lb = (x + y + 1) / 2;
                if lb > low {
                    low = lb;
                }
            }
            i += 1;
        }
        if low <= high {
            low as i32
        } else {
            -1
        }
    }
}

}
