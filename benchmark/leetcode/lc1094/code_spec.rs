use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn trip_load_at(trip: Vec<i32>, stop: int) -> int
        recommends
            trip@.len() == 3,
    {
        if trip@[1] as int <= stop && stop < trip@[2] as int {
            trip@[0] as int
        } else {
            0
        }
    }

    pub open spec fn load_prefix(trips: Seq<Vec<i32>>, n: int, stop: int) -> int
        recommends
            0 <= n <= trips.len(),
            0 <= stop <= 1000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            Self::load_prefix(trips, n - 1, stop) + Self::trip_load_at(trips[n - 1], stop)
        }
    }

    pub fn car_pooling(trips: Vec<Vec<i32>>, capacity: i32) -> (result: bool)
        requires
            1 <= trips.len() <= 1000,
            1 <= capacity <= 100_000,
            forall |i: int| 0 <= i < trips.len() ==> #[trigger] trips[i]@.len() == 3,
            forall |i: int| 0 <= i < trips.len() ==> 1 <= #[trigger] trips[i][0] <= 100,
            forall |i: int| 0 <= i < trips.len() ==> 0 <= #[trigger] trips[i][1] < trips[i][2] <= 1000,
        ensures
            result == (forall |stop: int| 0 <= stop <= 1000 ==> #[trigger] Self::load_prefix(trips@, trips.len() as int, stop) <= capacity as int),
    {
        let mut diff: Vec<i64> = Vec::new();
        let mut fill = 0usize;

        while fill < 1001 {
            diff.push(0);
            fill += 1;
        }

        let mut i = 0usize;
        while i < trips.len() {
            let passengers = trips[i][0] as i64;
            let from = trips[i][1] as usize;
            let to = trips[i][2] as usize;
            let add_value = diff[from] + passengers;
            let sub_value = diff[to] - passengers;

            diff.set(from, add_value);
            diff.set(to, sub_value);
            i += 1;
        }

        let mut current = 0i64;
        let mut stop = 0usize;
        while stop < 1001 {
            let next = current + diff[stop];
            current = next;
            if current > capacity as i64 {
                return false;
            }
            stop += 1;
        }

        true
    }
}

}
