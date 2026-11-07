impl Solution {
    pub fn min_total_meeting_distance(x1: i32, x2: i32, x3: i32) -> i32 {
        let mut coords: Vec<i32> = Vec::new();
        coords.push(x1);
        coords.push(x2);
        coords.push(x3);
        let mut mn = coords[0];
        let mut mx = coords[0];
        let mut i = 1usize;
        while i < 3 {
            if coords[i] < mn {
                mn = coords[i];
            }
            if coords[i] > mx {
                mx = coords[i];
            }
            i = i + 1;
        }
        mx - mn
    }
}
