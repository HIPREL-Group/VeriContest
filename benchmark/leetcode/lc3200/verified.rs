use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn height_from_spec(red: int, blue: int, row: int, red_turn: bool) -> int
        decreases red + blue + 1
    {
        if row <= 0 || red < 0 || blue < 0 {
            0
        } else if red_turn {
            if red < row {
                row - 1
            } else {
                Self::height_from_spec(red - row, blue, row + 1, false)
            }
        } else {
            if blue < row {
                row - 1
            } else {
                Self::height_from_spec(red, blue - row, row + 1, true)
            }
        }
    }

    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    fn height_from_exec(red: i32, blue: i32, row: i32, red_turn: bool) -> (h: i32)
        requires
            red >= 0,
            red <= 100,
            blue >= 0,
            blue <= 100,
            row >= 1,
        ensures
            h as int == Self::height_from_spec(red as int, blue as int, row as int, red_turn),
        decreases red + blue
    {
        if red_turn {
            if red < row {
                row - 1
            } else {
                Self::height_from_exec(red - row, blue, row + 1, false)
            }
        } else {
            if blue < row {
                row - 1
            } else {
                Self::height_from_exec(red, blue - row, row + 1, true)
            }
        }
    }

    pub fn max_height_of_triangle(red: i32, blue: i32) -> (result: i32)
        requires
            1 <= red <= 100,
            1 <= blue <= 100,
        ensures
            result as int == Self::max2(
                Self::height_from_spec(red as int, blue as int, 1, true),
                Self::height_from_spec(red as int, blue as int, 1, false),
            ),
    {
        let h1 = Self::height_from_exec(red, blue, 1, true);
        let h2 = Self::height_from_exec(red, blue, 1, false);
        if h1 >= h2 { h1 } else { h2 }
    }
}

}
