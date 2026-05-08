impl Solution {
    pub fn count_good_rectangles(rectangles: Vec<Vec<i32>>) -> i32
    {
        let mut cnt: i32 = 0;
        let mut mx: i32 = 0;
        let n = rectangles.len();
        let mut i = 0;
        while i < n
        {
            let l = rectangles[i][0];
            let w = rectangles[i][1];
            let side = if l <= w { l } else { w };
            if side > mx {
                cnt = 1;
                mx = side;
            } else if side == mx {
                cnt += 1;
            }
            i += 1;
        }
        cnt
    }
}
