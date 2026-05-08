impl Solution {
    pub fn area_of_max_diagonal(dimensions: Vec<Vec<i32>>) -> i32 {
        let mut best_diag: i32 = 0;
        let mut best_area: i32 = 0;
        let mut i: usize = 0;

        while i < dimensions.len() {
            let l: i32 = dimensions[i][0];
            let w: i32 = dimensions[i][1];
            let cur_diag: i32 = l * l + w * w;
            let cur_area: i32 = l * w;

            if cur_diag > best_diag || (cur_diag == best_diag && cur_area > best_area) {
                best_diag = cur_diag;
                best_area = cur_area;
            }

            i = i + 1;
        }

        best_area
    }
}
