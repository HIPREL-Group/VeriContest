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

    pub fn pivot_integer(n: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
        ensures
            result == -1 ==> forall|x: int| 1 <= x <= n as int ==> #[trigger] Self::sum_to(x) != Self::sum_to(n as int) - Self::sum_to(x - 1),
            result != -1 ==> 1 <= result <= n && Self::sum_to(result as int) == Self::sum_to(n as int) - Self::sum_to(result as int - 1),
    {
        let n_u = n as usize;
        let mut x: usize = 1;
        while x <= n_u {
            let mut left: i32 = 0;
            let mut i: usize = 1;
            while i <= x {
                left = left + i as i32;
                i = i + 1;
            }
            let mut right: i32 = 0;
            i = x;
            while i <= n_u {
                right = right + i as i32;
                i = i + 1;
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
