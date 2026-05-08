use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_eight_spec(money: int, children: int) -> int
        recommends
            1 <= money <= 200,
            2 <= children <= 30,
    {
        if money < children {
            -1
        } else {
            let rem = money - children;
            if rem / 7 == children && rem % 7 == 0 {
                children
            } else if rem / 7 == children - 1 && rem % 7 == 3 {
                children - 2
            } else if rem / 7 < children - 1 {
                rem / 7
            } else {
                children - 1
            }
        }
    }

    pub fn dist_money(money: i32, children: i32) -> (result: i32)
        requires
            1 <= money <= 200,
            2 <= children <= 30,
        ensures
            result as int == Self::max_eight_spec(money as int, children as int),
            -1 <= result as int <= children as int,
    {
        if money < children {
            proof {
                assert(Self::max_eight_spec(money as int, children as int) == -1);
            }
            return -1;
        }

        let rem = money - children;
        if rem / 7 == children && rem % 7 == 0 {
            proof {
                assert(Self::max_eight_spec(money as int, children as int) == children as int);
            }
            children
        } else if rem / 7 == children - 1 && rem % 7 == 3 {
            proof {
                assert(Self::max_eight_spec(money as int, children as int) == children as int - 2);
            }
            children - 2
        } else if rem / 7 < children - 1 {
            proof {
                assert(Self::max_eight_spec(money as int, children as int) == (rem / 7) as int);
            }
            rem / 7
        } else {
            proof {
                assert(Self::max_eight_spec(money as int, children as int) == children as int - 1);
            }
            children - 1
        }
    }
}

}
