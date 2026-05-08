use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_pair(a: int, b: int, num: int) -> bool {
    a >= 1 && b >= 1 && (a * b == num + 1 || a * b == num + 2)
}

pub open spec fn pair_diff(a: int, b: int) -> int {
    b - a
}

impl Solution {
    pub fn closest_divisors(num: i32) -> (res: Vec<i32>)
        requires
            1 <= num <= 1_000_000_000,
        ensures
            res.len() == 2,
            1 <= res[0] <= res[1],
            is_valid_pair(res[0] as int, res[1] as int, num as int),
            forall|a: int, b: int|
                1 <= a <= b && (a * b == (num as int) + 1 || a * b == (num as int) + 2) ==>
                    res[1] as int - res[0] as int <= #[trigger] pair_diff(a, b),
    {
        let mut i: i32 = 2;
        while i * i <= num + 2 {
            i += 1;
        }
        i -= 1;

        let mut best_a: i32 = 1;
        let mut best_b: i32 = num + 1;
        let mut found = false;

        while i >= 1 && !found {
            let n1 = num + 1;
            let n2 = num + 2;

            if n1 % i == 0 {
                best_a = i;
                best_b = n1 / i;
                found = true;
            } else if n2 % i == 0 {
                best_a = i;
                best_b = n2 / i;
                found = true;
            }

            if !found {
                i -= 1;
            }
        }

        vec![best_a, best_b]
    }
}

}
