use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_choice(k: int, b: int) -> bool {
    1 <= k && b % k == 0
}

pub open spec fn transformed_sum(a: int, b: int, k: int) -> int {
    a * k + b / k
}

impl Solution {
    pub fn maximum_even_sum(a: i128, b: i128) -> (res: i128)
        requires
            a >= 1,
            b >= 1,
            a <= 1000000000000000000,
            b <= 1000000000000000000,
            (a as int) * (b as int) <= 1000000000000000000,
        ensures
            res == -1 || (res >= 2 && res % 2 == 0),
            res != -1 ==> exists|k: int|
                #[trigger] valid_choice(k, b as int)
                && transformed_sum(a as int, b as int, k) == res,
            res != -1 ==> forall|k: int|
                valid_choice(k, b as int)
                && #[trigger] transformed_sum(a as int, b as int, k) % 2 == 0
                ==> transformed_sum(a as int, b as int, k) <= res,
            res == -1 ==> forall|k: int|
                #[trigger] valid_choice(k, b as int)
                ==> transformed_sum(a as int, b as int, k) % 2 != 0,
    {
        let mut k: i128 = 1;
        let mut found: bool = false;
        let mut best: i128 = -1;
        while k <= b {
            let cur_k = k;
            let mut cur_valid = false;
            let mut cur_even = false;
            let mut cur_sum: i128 = 0;
            if b % cur_k == 0 {
                cur_valid = true;
                let prod = a * cur_k;
                cur_sum = prod + b / cur_k;
                cur_even = cur_sum % 2 == 0;

                if cur_even {
                    if !found || cur_sum > best {
                        best = cur_sum;
                        found = true;
                    }
                }
            }
            k = k + 1;
        }
        if found {
            best
        } else {
            -1
        }
    }
}

}