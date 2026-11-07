impl Solution {
    pub fn queens_attackthe_king(queens: Vec<Vec<i32>>, king: Vec<i32>) -> Vec<Vec<i32>> {
        let kr = king[0];
        let kc = king[1];
        let n = queens.len();
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let qr = queens[i][0];
            let qc = queens[i][1];
            let dr: i32 = if qr > kr { qr - kr } else { kr - qr };
            let dc: i32 = if qc > kc { qc - kc } else { kc - qc };
            let on_line_check: bool = (qr == kr || qc == kc || dr == dc) && (qr != kr || qc != kc);
            if on_line_check {
                let sr_q: i32 = if qr > kr { 1 } else if qr < kr { -1 } else { 0 };
                let sc_q: i32 = if qc > kc { 1 } else if qc < kc { -1 } else { 0 };
                let q_dist: i32 = if dr >= dc { dr } else { dc };
                let mut blocked: bool = false;
                let mut j: usize = 0;
                while j < n {
                    if j != i {
                        let br = queens[j][0];
                        let bc = queens[j][1];
                        let bdr: i32 = if br > kr { br - kr } else { kr - br };
                        let bdc: i32 = if bc > kc { bc - kc } else { kc - bc };
                        let sr_b: i32 = if br > kr { 1 } else if br < kr { -1 } else { 0 };
                        let sc_b: i32 = if bc > kc { 1 } else if bc < kc { -1 } else { 0 };
                        let b_dist: i32 = if bdr >= bdc { bdr } else { bdc };
                        let b_on_line: bool = (br == kr || bc == kc || bdr == bdc) && (br != kr || bc != kc);
                        let is_block: bool = b_on_line && sr_b == sr_q && sc_b == sc_q && b_dist < q_dist;
                        if is_block {
                            blocked = true;
                        }
                    }
                    j = j + 1;
                }
                if !blocked {
                    let mut pair: Vec<i32> = Vec::new();
                    pair.push(qr);
                    pair.push(qc);
                    result.push(pair);
                }
            }
            i = i + 1;
        }
        result
    }
}
