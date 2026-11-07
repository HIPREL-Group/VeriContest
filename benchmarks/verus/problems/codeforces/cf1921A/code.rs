impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> i64 {
        let mut min_x = xs[0];
        let mut max_x = xs[0];
        let mut i = 1usize;
        while i < 4 {
            if xs[i] < min_x {
                min_x = xs[i];
            }
            if xs[i] > max_x {
                max_x = xs[i];
            }
            i = i + 1;
        }
        let mut min_y = ys[0];
        let mut max_y = ys[0];
        let mut j = 1usize;
        while j < 4 {
            if ys[j] < min_y {
                min_y = ys[j];
            }
            if ys[j] > max_y {
                max_y = ys[j];
            }
            j = j + 1;
        }
        let sx = max_x - min_x;
        let sy = max_y - min_y;
        sx * sy
    }
}
