impl Solution {
    pub fn min_rectangles_to_cover_points(points: Vec<Vec<i32>>, w: i32) -> i32 {
        let n = points.len();
        let mut xs: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            xs.push(points[i][0]);
            i = i + 1;
        }

        if n > 0 {
            let mut i2: usize = 1;
            while i2 < n {
                let mut j = i2;
                while j != 0 {
                    if xs[j - 1] > xs[j] {
                        let left = xs[j - 1];
                        let right = xs[j];
                        xs[j - 1] = right;
                        xs[j] = left;
                    }
                    j = j - 1;
                }
                i2 = i2 + 1;
            }
        }

        let mut ans: i32 = 0;
        let mut p: usize = 0;
        while p < n {
            let cover = xs[p] + w;
            p = p + 1;
            while p < n && xs[p] <= cover {
                p = p + 1;
            }
            ans = ans + 1;
        }

        ans
    }
}
