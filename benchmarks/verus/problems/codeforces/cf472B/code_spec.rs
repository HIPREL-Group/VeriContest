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

pub open spec fn count_floor_leq(floors: Seq<i32>, fl: int, idx: int) -> int
    recommends
        0 <= idx <= floors.len(),
    decreases
        floors.len() - idx,
{
    if idx >= floors.len() {
        0
    } else {
        (if (floors[idx] as int) <= fl { 1int } else { 0int }) + count_floor_leq(floors, fl, idx + 1)
    }
}

fn count_floor_eq_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> (r: usize)
    requires
        idx <= floors.len(),
        floors.len() <= 2000,
    ensures
        r as int == count_floor_eq(floors@, fl as int, idx as int),
        0 <= r as int <= floors.len() as int - idx as int,
    decreases
        floors.len() - idx,
{
    if idx >= floors.len() {
        0usize
    } else {
        let tail = count_floor_eq_exec(floors, fl, idx + 1);
        if floors[idx] == fl {
            1usize + tail
        } else {
            tail
        }
    }
}

fn count_floors_above_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> (r: usize)
    requires
        idx <= floors.len(),
        floors.len() <= 2000,
    ensures
        r as int == count_floors_above(floors@, fl as int, idx as int),
        0 <= r as int <= floors.len() as int - idx as int,
    decreases
        floors.len() - idx,
{
    if idx >= floors.len() {
        0usize
    } else {
        let tail = count_floors_above_exec(floors, fl, idx + 1);
        if floors[idx] > fl {
            1usize + tail
        } else {
            tail
        }
    }
}

fn same_floor_trips_exec(k: usize, floor: i32, remaining: usize, placed: usize) -> (r: i64)
    requires
        1 <= k <= 2000,
        2 <= floor <= 2000,
        placed + remaining <= 2000,
    ensures
        r as int == same_floor_trips(k as int, floor as int, remaining as int, placed as int),
        0 <= r as int <= remaining as int * 3998,
    decreases
        remaining,
{
    if remaining == 0 {
        0i64
    } else {
        let add = if placed % k == 0 {
            2 * ((floor as i64) - 1)
        } else {
            0i64
        };
        let tail = same_floor_trips_exec(k, floor, remaining - 1, placed + 1);
        add + tail
    }
}

fn elevator_total_exec(k: usize, floor: i32, floors: &Vec<i32>) -> (r: i64)
    requires
        1 <= k <= 2000,
        1 <= floors.len() <= 2000,
        0 <= floor <= 2000,
        forall|i: int| 0 <= i < floors.len() ==> 2 <= #[trigger] (floors[i] as int) <= 2000,
    ensures
        r as int == elevator_total_spec(k as int, floor as int, floors@),
        0 <= r as int,
    decreases
        floor + 1,
{
    if floor < 2 {
        0i64
    } else {
        let c = count_floor_eq_exec(floors, floor, 0);
        let pb = count_floors_above_exec(floors, floor, 0);
        let part = same_floor_trips_exec(k, floor, c, pb);
        let rest = elevator_total_exec(k, floor - 1, floors);
        let total = part + rest;
        total
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
        let ans = elevator_total_exec(k, 2000, &floors);
        ans
    }
}

}
