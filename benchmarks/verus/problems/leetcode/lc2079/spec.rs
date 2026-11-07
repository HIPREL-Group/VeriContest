use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn steps_spec(plants: Seq<i32>, capacity: i32, idx: int, current_water: int) -> int
        recommends
            0 <= idx <= plants.len(),
            forall|j: int| 0 <= j < plants.len() ==> 1 <= #[trigger] plants[j],
            forall|j: int| 0 <= j < plants.len() ==> #[trigger] plants[j] <= capacity,
            0 <= current_water <= capacity,
        decreases if plants.len() > idx { plants.len() - idx } else { 0int },
    {
        if idx >= plants.len() {
            0
        } else {
            if current_water < plants[idx] {
                (2 * idx + 1) + Self::steps_spec(plants, capacity, idx + 1, capacity - plants[idx] as int)
            } else {
                1 + Self::steps_spec(plants, capacity, idx + 1, current_water - plants[idx] as int)
            }
        }
    }

    pub fn watering_plants(plants: Vec<i32>, capacity: i32) -> (result: i32)
        requires
            1 <= plants.len() <= 1000,
            1 <= capacity <= 1000000000,
            forall|j: int| 0 <= j < plants.len() ==> 1 <= #[trigger] plants[j] <= 1000000,
            forall|j: int| 0 <= j < plants.len() ==> #[trigger] plants[j] <= capacity,
        ensures
            result == Self::steps_spec(plants@, capacity, 0, capacity as int),
    {
    }
}

}
