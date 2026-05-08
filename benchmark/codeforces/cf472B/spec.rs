use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_floor_eq(floors: Seq<i32>, fl: int, idx: int) -> int
    recommends
        0 <= idx <= floors.len(),
    decreases
        floors.len() - idx,
{
    if idx >= floors.len() {
        0
    } else if floors[idx] as int == fl {
        1 + count_floor_eq(floors, fl, idx + 1)
    } else {
        count_floor_eq(floors, fl, idx + 1)
    }
}

pub open spec fn count_floors_above(floors: Seq<i32>, f: int, idx: int) -> int
    recommends
        0 <= idx <= floors.len(),
    decreases
        floors.len() - idx,
{
    if idx >= floors.len() {
        0
    } else if (floors[idx] as int) > f {
        1 + count_floors_above(floors, f, idx + 1)
    } else {
        count_floors_above(floors, f, idx + 1)
    }
}

pub open spec fn same_floor_trips(k: int, floor: int, remaining: int, placed: int) -> int
    recommends
        1 <= k,
        2 <= floor,
        0 <= remaining,
        0 <= placed,
    decreases
        remaining,
{
    if remaining > 0 {
        let add = if (placed % k) == 0 {
            2 * (floor - 1)
        } else {
            0
        };
        add + same_floor_trips(k, floor, remaining - 1, placed + 1)
    } else {
        0
    }
}

pub open spec fn elevator_total_spec(k: int, floor: int, floors_seq: Seq<i32>) -> int
    recommends
        1 <= k <= 2000,
    decreases
        floor + 1,
{
    if floor < 2 {
        0
    } else {
        let c = count_floor_eq(floors_seq, floor, 0);
        let pb = count_floors_above(floors_seq, floor, 0);
        same_floor_trips(k, floor, c, pb) + elevator_total_spec(k, floor - 1, floors_seq)
    }
}

impl Solution {
    pub fn min_elevator_return_time(k: usize, floors: Vec<i32>) -> (res: i64)
        requires
            1 <= (k as int) && (k as int) <= 2000,
            1 <= floors.len() && floors.len() <= 2000,
            forall|i: int|
                0 <= i < floors.len() ==> 2 <= #[trigger] (floors[i] as int) && (floors[i] as int) <= 2000,
        ensures
            0 <= res,
            res as int == elevator_total_spec(k as int, 2000, floors@),
    {
    }
}

}
