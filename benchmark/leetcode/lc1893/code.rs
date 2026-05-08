impl Solution {
    pub fn is_covered(ranges: Vec<Vec<i32>>, left: i32, right: i32) -> bool {
        let mut i = left;
        while i <= right {
            let mut covered = false;
            let mut j = 0;
            while j < ranges.len() {
                if ranges[j][0] <= i && i <= ranges[j][1] {
                    covered = true;
                }
                j += 1;
            }
            if !covered {
                return false;
            }
            i += 1;
        }
        true
    }
}
