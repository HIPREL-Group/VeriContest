impl Solution {
    fn height_from_exec(red: i32, blue: i32, row: i32, red_turn: bool) -> i32 {
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

    pub fn max_height_of_triangle(red: i32, blue: i32) -> i32 {
        let h1 = Self::height_from_exec(red, blue, 1, true);
        let h2 = Self::height_from_exec(red, blue, 1, false);
        if h1 >= h2 { h1 } else { h2 }
    }
}
