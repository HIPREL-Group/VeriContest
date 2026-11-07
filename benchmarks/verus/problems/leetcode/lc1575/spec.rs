use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn dp(locs: Seq<i32>, n: int, city: int, finish: int, fuel: int, j: int) -> int
        decreases fuel, n - j,
    {
        if fuel < 0 {
            0int
        } else if j >= n {
            if city == finish { 1int } else { 0int }
        } else if j == city {
            Self::dp(locs, n, city, finish, fuel, j + 1)
        } else {
            let cost = Self::abs_diff(locs[city] as int, locs[j] as int);
            if cost >= 1 && cost <= fuel {
                Self::dp(locs, n, j, finish, fuel - cost, 0)
                    + Self::dp(locs, n, city, finish, fuel, j + 1)
            } else {
                Self::dp(locs, n, city, finish, fuel, j + 1)
            }
        }
    }

    pub fn count_routes(locations: Vec<i32>, start: i32, finish: i32, fuel: i32) -> (result: i32)
        requires
            2 <= locations.len() <= 100,
            forall |i: int| 0 <= i < locations.len() ==> 1 <= #[trigger] locations[i] <= 1_000_000_000,
            forall |i: int, j: int| #![trigger locations[i], locations[j]] 0 <= i && i < j && j < locations.len() ==> locations[i] != locations[j],
            0 <= start < locations.len(),
            0 <= finish < locations.len(),
            1 <= fuel <= 200,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::dp(
                locations@,
                locations.len() as int,
                start as int,
                finish as int,
                fuel as int,
                0int,
            ) % 1_000_000_007,
    {
    }
}

} 
