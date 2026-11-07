impl Solution {
    pub fn flip_lights(n: i32, presses: i32) -> i32
    {
        if presses == 0 {
            return 1;
        }
        if n == 1 {
            return 2;
        }
        if n == 2 {
            if presses == 1 {
                return 3;
            }
            return 4;
        }
        if presses == 1 {
            return 4;
        }
        if presses == 2 {
            return 7;
        }
        return 8;
    }
}
