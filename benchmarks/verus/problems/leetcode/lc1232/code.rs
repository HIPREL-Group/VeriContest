impl Solution {
    pub fn check_straight_line(coordinates: Vec<Vec<i32>>) -> bool {
        let x0 = coordinates[0][0];
        let y0 = coordinates[0][1];
        let x1 = coordinates[1][0];
        let y1 = coordinates[1][1];
        let dx = x1 - x0;
        let dy = y1 - y0;
        
        let mut i = 2;
        while i < coordinates.len() {
            let xi = coordinates[i][0];
            let yi = coordinates[i][1];
            if (dy as i64) * ((xi - x0) as i64) != ((yi - y0) as i64) * (dx as i64) {
                return false;
            }
            i += 1;
        }
        
        true
    }
}
