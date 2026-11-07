impl Solution {
    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> i32 {
        let n = points.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                let mut pair_valid = false;
                if i != j {
                    let x1 = points[i][0];
                    let y1 = points[i][1];
                    let x2 = points[j][0];
                    let y2 = points[j][1];
                    if x1 <= x2 && y1 >= y2 {
                        let mut ok = true;
                        let mut k: usize = 0;
                        while k < n {
                            let mut is_block = false;
                            if k != i && k != j {
                                let x3 = points[k][0];
                                let y3 = points[k][1];
                                if x1 <= x3 && x3 <= x2 && y2 <= y3 && y3 <= y1 {
                                    is_block = true;
                                }
                            }
                            ok = ok && !is_block;
                            k += 1;
                        }
                        pair_valid = ok;
                    }
                }
                let add: i32 = if pair_valid { 1 } else { 0 };
                ans += add;
                j += 1;
            }
            i += 1;
        }

        ans
    }
}
