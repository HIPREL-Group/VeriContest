impl Solution {
    pub fn image_smoother(img: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let rows = img.len();
        let cols = img[0].len();
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols {
                let top = if i > 0 { i - 1 } else { 0 };
                let bottom = if i + 2 <= rows { i + 2 } else { rows };
                let left = if j > 0 { j - 1 } else { 0 };
                let right = if j + 2 <= cols { j + 2 } else { cols };
                let mut sum: i32 = 0;
                let mut count: i32 = 0;
                let mut x: usize = top;
                while x < bottom {
                    let mut y: usize = left;
                    while y < right {
                        let v = img[x][y];
                        sum = sum + v;
                        count = count + 1;
                        y += 1;
                    }
                    x += 1;
                }
                let avg = sum / count;
                row.push(avg);
                j += 1;
            }
            result.push(row);
            i += 1;
        }
        result
    }
}
