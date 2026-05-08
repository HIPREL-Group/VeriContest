impl Solution {
    pub fn find_closest(x: i32, y: i32, z: i32) -> i32 {
        let dx = if x >= z {
            x - z
        } else {
            z - x
        };
        let dy = if y >= z {
            y - z
        } else {
            z - y
        };
        if dx < dy {
            1
        } else if dy < dx {
            2
        } else {
            0
        }
    }
}
