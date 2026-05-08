fn count_floor_eq_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> usize {
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

fn count_floors_above_exec(floors: &Vec<i32>, fl: i32, idx: usize) -> usize {
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

fn same_floor_trips_exec(k: usize, floor: i32, remaining: usize, placed: usize) -> i64 {
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

fn elevator_total_exec(k: usize, floor: i32, floors: &Vec<i32>) -> i64 {
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
    pub fn min_elevator_return_time(k: usize, floors: Vec<i32>) -> i64 {
        let ans = elevator_total_exec(k, 2000, &floors);
        ans
    }
}
