impl Solution {
    pub fn construct_rectangle(area: i32) -> Vec<i32> {
        let mut best_l: i32 = area;
        let mut best_w: i32 = 1;
        let mut w: i32 = 1;

        while w <= area {
            if area % w == 0 && area / w >= w {
                best_l = area / w;
                best_w = w;
            }
            w += 1;
        }

        vec![best_l, best_w]
    }
}
