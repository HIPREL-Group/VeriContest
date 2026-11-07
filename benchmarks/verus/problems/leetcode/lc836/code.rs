impl Solution {
    pub fn is_rectangle_overlap(rec1: Vec<i32>, rec2: Vec<i32>) -> bool {
        let (x1_1, y1_1, x2_1, y2_1 ) = (rec1[0], rec1[1], rec1[2], rec1[3]);
        let (x1_2, y1_2, x2_2, y2_2 ) = (rec2[0], rec2[1], rec2[2], rec2[3]);

        if x1_1 >= x2_2 || y1_1 >= y2_2 { return false; }
        if x1_2 >= x2_1 || y1_2 >= y2_1 { return false; }

        return true;
    }
}