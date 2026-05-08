impl Solution {
    pub fn spiral_order(matrix: Vec<Vec<i32>>) -> Vec<i32> {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut result: Vec<i32> = Vec::new();
        let mut top: usize = 0;
        let mut bottom: usize = rows;
        let mut left: usize = 0;
        let mut right: usize = cols;

        while top < bottom && left < right {
            let layer_top = top;
            let layer_bottom = bottom;
            let layer_left = left;
            let layer_right = right;
            let mut c: usize = left;
            while c < right {
                let v = matrix[top][c];
                result.push(v);
                c += 1;
            }
            top += 1;

            let mut r: usize = top;
            while r < bottom {
                let v = matrix[r][right - 1];
                result.push(v);
                r += 1;
            }
            right -= 1;

            if top < bottom {
                let mut c2: usize = right;
                while c2 > left {
                    c2 -= 1;
                    let v = matrix[bottom - 1][c2];
                    result.push(v);
                }
                bottom -= 1;
            }

            if left < right {
                let mut r2: usize = bottom;
                while r2 > top {
                    r2 -= 1;
                    let v = matrix[r2][left];
                    result.push(v);
                }
                left += 1;
            }

        }

        result
    }
}
