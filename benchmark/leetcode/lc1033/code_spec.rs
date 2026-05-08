use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min3(a: int, b: int, c: int) -> int {
    if a <= b && a <= c { a }
    else if b <= c { b }
    else { c }
}

pub open spec fn mid3(a: int, b: int, c: int) -> int {
    if (a <= b && b <= c) || (c <= b && b <= a) { b }
    else if (b <= a && a <= c) || (c <= a && a <= b) { a }
    else { c }
}

pub open spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

pub open spec fn spec_min_moves(a: int, b: int, c: int) -> int {
    let lo = min3(a, b, c);
    let mi = mid3(a, b, c);
    let hi = max3(a, b, c);
    if mi - lo == 1 && hi - mi == 1 {
        0
    } else if mi - lo <= 2 || hi - mi <= 2 {
        1
    } else {
        2
    }
}

pub open spec fn spec_max_moves(a: int, b: int, c: int) -> int {
    max3(a, b, c) - min3(a, b, c) - 2
}

impl Solution {
    pub fn num_moves_stones(a: i32, b: i32, c: i32) -> (result: Vec<i32>)
        requires
            1 <= a <= 100,
            1 <= b <= 100,
            1 <= c <= 100,
            a != b,
            b != c,
            a != c,
        ensures
            result.len() == 2,
            result[0] == spec_min_moves(a as int, b as int, c as int),
            result[1] == spec_max_moves(a as int, b as int, c as int),
    {
        let mut x = a;
        let mut y = b;
        let mut z = c;
        if x > y {
            let tmp = x;
            x = y;
            y = tmp;
        }
        if x > z {
            let tmp = x;
            x = z;
            z = tmp;
        }
        if y > z {
            let tmp = y;
            y = z;
            z = tmp;
        }
        let min_moves;
        if y - x == 1 && z - y == 1 {
            min_moves = 0;
        } else if y - x <= 2 || z - y <= 2 {
            min_moves = 1;
        } else {
            min_moves = 2;
        }
        let max_moves = z - x - 2;
        let mut result = Vec::new();
        result.push(min_moves);
        result.push(max_moves);
        result
    }
}

}
