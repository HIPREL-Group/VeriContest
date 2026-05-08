use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn max_containers_spec(n: int, w: int, max_weight: int) -> int {
        let area = n * n;
        let by_weight = max_weight / w;
        if area <= by_weight {
            area
        } else {
            by_weight
        }
    }

    pub fn max_containers(n: i32, w: i32, max_weight: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= w <= 1000,
            1 <= max_weight <= 1_000_000_000,
        ensures
            result as int == Self::max_containers_spec(n as int, w as int, max_weight as int),
    {
        assert(0 < n * n <= 1_000_000) by (nonlinear_arith)
            requires
                1 <= n <= 1000,
        {
        }
        let area = n * n;
        let by_weight = max_weight / w;

        assert(area as int == n as int * n as int);
        assert(by_weight as int == max_weight as int / w as int);

        if area <= by_weight {
            assert(Self::max_containers_spec(n as int, w as int, max_weight as int) == area as int);
            area
        } else {
            assert(Self::max_containers_spec(n as int, w as int, max_weight as int) == by_weight as int);
            by_weight
        }
    }
}

}
