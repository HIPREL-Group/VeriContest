use std::io;

pub struct Solution;

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

fn main() {
    let mut line = String::new();
    io::stdin().read_line(&mut line).expect("read");
    let mut it = line.split_whitespace();
    let n: usize = it.next().unwrap().parse().expect("n");
    let k: usize = it.next().unwrap().parse().expect("k");
    line.clear();
    io::stdin().read_line(&mut line).expect("read");
    let mut floors: Vec<i32> = Vec::new();
    let mut parts = line.split_whitespace();
    let mut i = 0usize;
    while i < n {
        let v: i32 = parts.next().unwrap().parse().expect("f");
        floors.push(v);
        i = i + 1;
    }
    println!("{}", Solution::min_elevator_return_time(k, floors));
}
