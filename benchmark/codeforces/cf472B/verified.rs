use vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way;
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

proof fn lemma_count_floor_eq_bounds(floors: Seq<i32>, fl: int, idx: int)
    requires
        0 <= idx <= floors.len(),
    ensures
        0 <= count_floor_eq(floors, fl, idx),
        count_floor_eq(floors, fl, idx) <= floors.len() - idx,
    decreases
        floors.len() - idx,
{
    if idx < floors.len() {
        lemma_count_floor_eq_bounds(floors, fl, idx + 1);
        if floors[idx] as int == fl {
            assert(count_floor_eq(floors, fl, idx) == 1 + count_floor_eq(floors, fl, idx + 1));
        } else {
            assert(count_floor_eq(floors, fl, idx) == count_floor_eq(floors, fl, idx + 1));
        }
    }
}

proof fn lemma_count_floors_above_bounds(floors: Seq<i32>, fl: int, idx: int)
    requires
        0 <= idx <= floors.len(),
    ensures
        0 <= count_floors_above(floors, fl, idx),
        count_floors_above(floors, fl, idx) <= floors.len() - idx,
    decreases
        floors.len() - idx,
{
    if idx < floors.len() {
        lemma_count_floors_above_bounds(floors, fl, idx + 1);
        if (floors[idx] as int) > fl {
            assert(count_floors_above(floors, fl, idx) == 1 + count_floors_above(floors, fl, idx + 1));
        } else {
            assert(count_floors_above(floors, fl, idx) == count_floors_above(floors, fl, idx + 1));
        }
    }
}

proof fn lemma_same_floor_trips_bounds(k: int, floor: int, remaining: int, placed: int)
    requires
        1 <= k,
        2 <= floor <= 2000,
        0 <= remaining,
        0 <= placed,
    ensures
        0 <= same_floor_trips(k, floor, remaining, placed),
        same_floor_trips(k, floor, remaining, placed) <= remaining * 3998,
    decreases
        remaining,
{
    if remaining > 0 {
        lemma_same_floor_trips_bounds(k, floor, remaining - 1, placed + 1);
        let add = if (placed % k) == 0 {
            2 * (floor - 1)
        } else {
            0
        };
        assert(0 <= add <= 2 * (floor - 1));
        assert(2 * (floor - 1) <= 3998);
        assert(same_floor_trips(k, floor, remaining, placed)
            == add + same_floor_trips(k, floor, remaining - 1, placed + 1));
        assert(remaining * 3998 == 3998 + (remaining - 1) * 3998);
        assert(add + same_floor_trips(k, floor, remaining - 1, placed + 1) <= remaining * 3998);
    }
}

proof fn lemma_count_floor_leq_bounds(floors: Seq<i32>, fl: int, idx: int)
    requires
        0 <= idx <= floors.len(),
    ensures
        0 <= count_floor_leq(floors, fl, idx),
        count_floor_leq(floors, fl, idx) <= floors.len() - idx,
    decreases
        floors.len() - idx,
{
    if idx < floors.len() {
        lemma_count_floor_leq_bounds(floors, fl, idx + 1);
        if (floors[idx] as int) <= fl {
            assert(count_floor_leq(floors, fl, idx) == 1 + count_floor_leq(floors, fl, idx + 1));
        } else {
            assert(count_floor_leq(floors, fl, idx) == count_floor_leq(floors, fl, idx + 1));
        }
    }
}

proof fn lemma_count_floor_leq_split(floors: Seq<i32>, floor: int, idx: int)
    requires
        2 <= floor <= 2000,
        0 <= idx <= floors.len(),
        forall|i: int| 0 <= i < floors.len() ==> 2 <= #[trigger] (floors[i] as int) <= 2000,
    ensures
        count_floor_leq(floors, floor, idx)
            == count_floor_eq(floors, floor, idx) + count_floor_leq(floors, floor - 1, idx),
    decreases
        floors.len() - idx,
{
    if idx < floors.len() {
        lemma_count_floor_leq_split(floors, floor, idx + 1);
        if floors[idx] as int == floor {
            assert(count_floor_leq(floors, floor, idx) == 1 + count_floor_leq(floors, floor, idx + 1));
            assert(count_floor_eq(floors, floor, idx) == 1 + count_floor_eq(floors, floor, idx + 1));
            assert(count_floor_leq(floors, floor - 1, idx) == count_floor_leq(floors, floor - 1, idx + 1));
        } else if (floors[idx] as int) < floor {
            assert((floors[idx] as int) <= floor - 1);
            assert(count_floor_leq(floors, floor, idx) == 1 + count_floor_leq(floors, floor, idx + 1));
            assert(count_floor_eq(floors, floor, idx) == count_floor_eq(floors, floor, idx + 1));
            assert(count_floor_leq(floors, floor - 1, idx) == 1 + count_floor_leq(floors, floor - 1, idx + 1));
        } else {
            assert(count_floor_leq(floors, floor, idx) == count_floor_leq(floors, floor, idx + 1));
            assert(count_floor_eq(floors, floor, idx) == count_floor_eq(floors, floor, idx + 1));
            assert(count_floor_leq(floors, floor - 1, idx) == count_floor_leq(floors, floor - 1, idx + 1));
        }
    }
}

proof fn lemma_count_partition_above_leq(floors: Seq<i32>, floor: int, idx: int)
    requires
        0 <= idx <= floors.len(),
    ensures
        count_floors_above(floors, floor, idx) + count_floor_leq(floors, floor, idx) == floors.len() - idx,
    decreases
        floors.len() - idx,
{
    if idx < floors.len() {
        lemma_count_partition_above_leq(floors, floor, idx + 1);
        if (floors[idx] as int) > floor {
            assert(count_floors_above(floors, floor, idx) == 1 + count_floors_above(floors, floor, idx + 1));
            assert(count_floor_leq(floors, floor, idx) == count_floor_leq(floors, floor, idx + 1));
        } else {
            assert(count_floors_above(floors, floor, idx) == count_floors_above(floors, floor, idx + 1));
            assert(count_floor_leq(floors, floor, idx) == 1 + count_floor_leq(floors, floor, idx + 1));
        }
    }
}

proof fn lemma_elevator_total_spec_bounds(k: int, floor: int, floors: Seq<i32>)
    requires
        1 <= k <= 2000,
        0 <= floor <= 2000,
        forall|i: int| 0 <= i < floors.len() ==> 2 <= #[trigger] (floors[i] as int) <= 2000,
    ensures
        0 <= elevator_total_spec(k, floor, floors),
        elevator_total_spec(k, floor, floors) <= count_floor_leq(floors, floor, 0) * 3998,
    decreases
        floor + 1,
{
    if floor >= 2 {
        lemma_count_floor_eq_bounds(floors, floor, 0);
        lemma_count_floors_above_bounds(floors, floor, 0);
        lemma_count_floor_leq_bounds(floors, floor, 0);
        lemma_count_floor_leq_bounds(floors, floor - 1, 0);
        lemma_count_floor_leq_split(floors, floor, 0);
        lemma_same_floor_trips_bounds(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0));
        lemma_elevator_total_spec_bounds(k, floor - 1, floors);
        assert(elevator_total_spec(k, floor, floors)
            == same_floor_trips(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0))
                + elevator_total_spec(k, floor - 1, floors));
        assert(same_floor_trips(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0))
            <= count_floor_eq(floors, floor, 0) * 3998);
        assert(elevator_total_spec(k, floor - 1, floors) <= count_floor_leq(floors, floor - 1, 0) * 3998);
        assert(
            same_floor_trips(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0))
                + elevator_total_spec(k, floor - 1, floors)
                <= count_floor_eq(floors, floor, 0) * 3998 + count_floor_leq(floors, floor - 1, 0) * 3998
        );
        assert(
            count_floor_leq(floors, floor, 0)
                == count_floor_eq(floors, floor, 0) + count_floor_leq(floors, floor - 1, 0)
        );
        assert(elevator_total_spec(k, floor, floors) <= count_floor_leq(floors, floor, 0) * 3998) by {
            assert(elevator_total_spec(k, floor, floors)
                == same_floor_trips(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0))
                    + elevator_total_spec(k, floor - 1, floors));
            assert(same_floor_trips(k, floor, count_floor_eq(floors, floor, 0), count_floors_above(floors, floor, 0))
                <= count_floor_eq(floors, floor, 0) * 3998);
            assert(elevator_total_spec(k, floor - 1, floors) <= count_floor_leq(floors, floor - 1, 0) * 3998);
            lemma_mul_is_distributive_add_other_way(
                count_floor_eq(floors, floor, 0),
                count_floor_leq(floors, floor - 1, 0),
                3998,
            );
        }
    } else {
        lemma_count_floor_leq_bounds(floors, floor, 0);
        assert(elevator_total_spec(k, floor, floors) == 0);
        assert(0 <= count_floor_leq(floors, floor, 0) * 3998);
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
            proof {
                assert(count_floor_eq(floors@, fl as int, idx as int)
                    == 1 + count_floor_eq(floors@, fl as int, idx as int + 1));
                assert(tail as int == count_floor_eq(floors@, fl as int, idx as int + 1));
                assert(tail as int <= floors.len() as int - (idx as int + 1));
                assert(1 + tail as int <= floors.len() as int - idx as int);
            }
            1usize + tail
        } else {
            proof {
                assert(count_floor_eq(floors@, fl as int, idx as int)
                    == count_floor_eq(floors@, fl as int, idx as int + 1));
            }
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
            proof {
                assert(count_floors_above(floors@, fl as int, idx as int)
                    == 1 + count_floors_above(floors@, fl as int, idx as int + 1));
                assert(tail as int == count_floors_above(floors@, fl as int, idx as int + 1));
                assert(tail as int <= floors.len() as int - (idx as int + 1));
                assert(1 + tail as int <= floors.len() as int - idx as int);
            }
            1usize + tail
        } else {
            proof {
                assert(count_floors_above(floors@, fl as int, idx as int)
                    == count_floors_above(floors@, fl as int, idx as int + 1));
            }
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
        proof {
            assert(remaining > 0);
            assert(tail as int == same_floor_trips(k as int, floor as int, remaining as int - 1, placed as int + 1));
            assert(0 <= tail as int <= (remaining as int - 1) * 3998);
            if placed % k == 0 {
                assert(add as int == 2 * (floor as int - 1));
            } else {
                assert(add as int == 0);
            }
            assert(0 <= add as int <= 2 * (floor as int - 1));
            assert(2 * (floor as int - 1) <= 3998);
            assert(same_floor_trips(k as int, floor as int, remaining as int, placed as int)
                == add as int + same_floor_trips(k as int, floor as int, remaining as int - 1, placed as int + 1));
            assert(remaining as int * 3998 == 3998 + (remaining as int - 1) * 3998);
            assert(add as int + tail as int <= remaining as int * 3998);
            assert(remaining as int <= 2000);
            assert(add as int + tail as int <= 2000 * 3998);
        }
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
        proof {
            lemma_count_floor_eq_bounds(floors@, floor as int, 0);
            lemma_count_floors_above_bounds(floors@, floor as int, 0);
            lemma_count_floor_leq_bounds(floors@, floor as int, 0);
            lemma_count_floor_leq_bounds(floors@, floor as int - 1, 0);
            lemma_count_partition_above_leq(floors@, floor as int, 0);
            lemma_count_floor_leq_split(floors@, floor as int, 0);
            assert(c as int == count_floor_eq(floors@, floor as int, 0));
            assert(pb as int == count_floors_above(floors@, floor as int, 0));
            assert(
                count_floor_leq(floors@, floor as int, 0)
                    == count_floor_eq(floors@, floor as int, 0) + count_floor_leq(floors@, floor as int - 1, 0)
            );
            assert(0 <= count_floor_leq(floors@, floor as int - 1, 0));
            assert(c as int <= count_floor_leq(floors@, floor as int, 0));
            assert(pb as int + count_floor_leq(floors@, floor as int, 0) == floors.len());
            assert(pb as int + c as int <= floors.len());
            assert(floors.len() <= 2000);
            assert(pb as int + c as int <= 2000);
            assert(pb + c <= 2000usize);
        }
        let part = same_floor_trips_exec(k, floor, c, pb);
        let rest = elevator_total_exec(k, floor - 1, floors);
        proof {
            lemma_same_floor_trips_bounds(k as int, floor as int, c as int, pb as int);
            lemma_elevator_total_spec_bounds(k as int, floor as int - 1, floors@);
            assert(part as int == same_floor_trips(k as int, floor as int, c as int, pb as int));
            assert(part as int == same_floor_trips(
                k as int,
                floor as int,
                count_floor_eq(floors@, floor as int, 0),
                count_floors_above(floors@, floor as int, 0),
            ));
            assert(rest as int == elevator_total_spec(k as int, floor as int - 1, floors@));
            assert(part as int <= c as int * 3998);
            assert(rest as int <= count_floor_leq(floors@, floor as int - 1, 0) * 3998);
            assert(
                count_floor_leq(floors@, floor as int, 0)
                    == count_floor_eq(floors@, floor as int, 0) + count_floor_leq(floors@, floor as int - 1, 0)
            );
            assert(part as int + rest as int <= c as int * 3998 + count_floor_leq(floors@, floor as int - 1, 0) * 3998);
            assert(c as int * 3998 + count_floor_leq(floors@, floor as int - 1, 0) * 3998
                == (c as int + count_floor_leq(floors@, floor as int - 1, 0)) * 3998);
            assert(part as int + rest as int <= count_floor_leq(floors@, floor as int, 0) * 3998);
            assert(count_floor_leq(floors@, floor as int, 0) <= floors.len());
            assert(part as int + rest as int <= 2000 * 3998);
            assert(elevator_total_spec(k as int, floor as int, floors@)
                == same_floor_trips(
                    k as int,
                    floor as int,
                    count_floor_eq(floors@, floor as int, 0),
                    count_floors_above(floors@, floor as int, 0),
                ) + elevator_total_spec(k as int, floor as int - 1, floors@));
        }
        let total = part + rest;
        proof {
            assert(total as int == part as int + rest as int);
            assert(0 <= total as int);
            assert(total as int == elevator_total_spec(k as int, floor as int, floors@));
        }
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
        proof {
            assert(ans as int == elevator_total_spec(k as int, 2000, floors@));
        }
        ans
    }
}

}
