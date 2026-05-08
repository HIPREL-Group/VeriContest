impl Solution {
    pub fn is_self_crossing(distance: Vec<i32>) -> bool {
        let n = distance.len();
        if n < 4 {
            return false;
        }
        let mut i: usize = 3;

        while i < n {
            let di = distance[i] as i64;
            let d_im1 = distance[i - 1] as i64;
            let d_im2 = distance[i - 2] as i64;
            let d_im3 = distance[i - 3] as i64;

            if di >= d_im2 && d_im1 <= d_im3 {
                return true;
            }

            if i >= 4 {
                let d_im4 = distance[i - 4] as i64;
                if d_im1 == d_im3 && di + d_im4 >= d_im2 {
                    return true;
                }
            }

            if i >= 5 {
                let d_im4 = distance[i - 4] as i64;
                let d_im5 = distance[i - 5] as i64;
                if d_im2 >= d_im4
                    && d_im1 <= d_im3
                    && d_im1 + d_im5 >= d_im3
                    && di + d_im4 >= d_im2
                {
                    return true;
                }
            }

            i += 1;
        }

        false
    }
}
