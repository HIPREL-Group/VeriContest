impl Solution {
    pub fn max(x: i32, y: i32) -> i32
    {
        if x >= y { x as i32 } else { y as i32 }
    }

    pub fn min(x: i32, y: i32) -> i32
    {
        if x <= y { x as i32} else { y as i32 }
    }

    pub fn compute_area(ax1: i32, ay1: i32, ax2: i32, ay2: i32, bx1: i32, by1: i32, bx2: i32, by2: i32) -> i32
    {
        let area1 = (ax2 - ax1) * (ay2 - ay1);
        let area2 = (bx2 - bx1) * (by2 - by1);
        let overlap_x = Self::max(0, Self::min(ax2, bx2) - Self::max(ax1, bx1));
        let overlap_y = Self::max(0, Self::min(ay2, by2) - Self::max(ay1, by1));
        let intersection = overlap_x * overlap_y;
        return area1 + area2 - intersection;
    }
}
