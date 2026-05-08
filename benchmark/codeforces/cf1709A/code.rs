impl Solution {
    pub fn can_open_all_doors(x: i32, a: i32, b: i32, c: i32) -> bool {
        let y = if x == 1 {
            a
        } else if x == 2 {
            b
        } else {
            c
        };
        if y == 0 {
            false
        } else {
            let z = if y == 1 {
                a
            } else if y == 2 {
                b
            } else {
                c
            };
            z != 0
        }
    }
}
