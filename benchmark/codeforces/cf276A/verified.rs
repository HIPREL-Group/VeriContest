use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn joy_value(f: int, t: int, k: int) -> int {
        if t <= k {
            f
        } else {
            f - t + k
        }
    }

    pub fn max_lunch_joy(restaurants: Vec<(i64, i64)>, k: i64) -> (result: i64)
        requires
            restaurants.len() >= 1,
            restaurants.len() <= 10000,
            1 <= k <= 1000000000,
            forall |i: int| 0 <= i < restaurants.len() ==>
                1 <= #[trigger] restaurants@[i].0 <= 1000000000,
            forall |i: int| 0 <= i < restaurants.len() ==>
                1 <= #[trigger] restaurants@[i].1 <= 1000000000,
        ensures
            forall |i: int| 0 <= i < restaurants.len() ==>
                result >= Self::joy_value(restaurants@[i].0 as int, restaurants@[i].1 as int, k as int),
            exists |i: int| 0 <= i < restaurants.len() &&
                result == Self::joy_value(restaurants@[i].0 as int, restaurants@[i].1 as int, k as int),
    {
        let n = restaurants.len();
        let f0 = restaurants[0].0;
        let t0 = restaurants[0].1;
        let mut max_joy: i64 = if t0 <= k { f0 } else { f0 - t0 + k };
        let ghost mut witness: int = 0;

        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == restaurants.len(),
                restaurants.len() >= 1,
                restaurants.len() <= 10000,
                1 <= k <= 1000000000,
                forall |j: int| 0 <= j < restaurants.len() ==>
                    1 <= #[trigger] restaurants@[j].0 <= 1000000000,
                forall |j: int| 0 <= j < restaurants.len() ==>
                    1 <= #[trigger] restaurants@[j].1 <= 1000000000,
                forall |j: int| 0 <= j < i as int ==>
                    max_joy as int >= Self::joy_value(restaurants@[j].0 as int, restaurants@[j].1 as int, k as int),
                0 <= witness < i as int,
                max_joy as int == Self::joy_value(restaurants@[witness].0 as int, restaurants@[witness].1 as int, k as int),
            decreases n - i,
        {
            let f = restaurants[i].0;
            let t = restaurants[i].1;
            let joy: i64 = if t <= k { f } else { f - t + k };

            proof {
                assert(joy as int == Self::joy_value(f as int, t as int, k as int));
            }

            if joy > max_joy {
                max_joy = joy;
                proof {
                    witness = i as int;
                }
            }

            proof {
                assert forall |j: int| 0 <= j < i as int + 1 implies
                    max_joy as int >= Self::joy_value(restaurants@[j].0 as int, restaurants@[j].1 as int, k as int) by {
                    if j < i as int {
                    } else {
                        assert(j == i as int);
                    }
                }
            }

            i = i + 1;
        }

        proof {
            assert(i == n);
            assert(0 <= witness && witness < restaurants.len());
            assert(max_joy as int == Self::joy_value(restaurants@[witness].0 as int, restaurants@[witness].1 as int, k as int));
        }

        max_joy
    }
}

}
