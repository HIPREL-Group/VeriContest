use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sum_to(end: int) -> int
        decreases end
    {
        if end <= 0 { 0 }
        else { Self::sum_to(end - 1) + end }
    }

    proof fn sum_to_bound(x: int)
        requires 0 <= x <= 1000,
        ensures 0 <= Self::sum_to(x) <= x * 1001,
        decreases x,
    {
        if x > 0 {
            Self::sum_to_bound(x - 1);
        }
    }

    pub fn pivot_integer(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result == -1 ==> forall|x: int| 1 <= x <= n as int ==> #[trigger] Self::sum_to(x) != Self::sum_to(n as int) - Self::sum_to(x - 1),
            result != -1 ==> 1 <= result <= n && Self::sum_to(result as int) == Self::sum_to(n as int) - Self::sum_to(result as int - 1),
    {
        let n_u = n as usize;
        let mut x: usize = 1;
        while x <= n_u
            invariant
                1 <= x <= n_u + 1,
                1 <= n <= 1000,
                n_u == n as usize,
                n_u <= 1000,
                forall|y: int| 1 <= y < x as int ==> #[trigger] Self::sum_to(y) != Self::sum_to(n as int) - Self::sum_to(y - 1),
            decreases n_u + 1 - x
        {
            let mut left: i32 = 0;
            let mut i: usize = 1;
            while i <= x
                invariant
                    1 <= i <= x + 1,
                    x <= n_u,
                    n_u <= 1000,
                    1 <= n <= 1000,
                    n_u == n as usize,
                    left as int == Self::sum_to(i as int - 1),
                    0 <= left <= 1_001_000,
                decreases x + 1 - i
            {
                proof { Self::sum_to_bound(i as int); }
                left = left + i as i32;
                i = i + 1;
            }

            let mut right: i32 = 0;
            i = x;
            while i <= n_u
                invariant
                    1 <= x <= n_u,
                    x <= i <= n_u + 1,
                    n_u <= 1000,
                    1 <= n <= 1000,
                    n_u == n as usize,
                    right as int == Self::sum_to(i as int - 1) - Self::sum_to(x as int - 1),
                    0 <= right <= 1_001_000,
                decreases n_u + 1 - i
            {
                proof {
                    Self::sum_to_bound(i as int);
                    Self::sum_to_bound(x as int - 1);
                }
                right = right + i as i32;
                i = i + 1;
            }

            proof {
                assert(left as int == Self::sum_to(x as int));
                assert(right as int == Self::sum_to(n as int) - Self::sum_to(x as int - 1));
            }

            if left == right {
                return x as i32;
            }
            x = x + 1;
        }
        -1
    }
}

}
