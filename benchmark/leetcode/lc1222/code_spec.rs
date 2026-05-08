use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn sign_val(x: int) -> int {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

pub open spec fn on_line(qr: int, qc: int, kr: int, kc: int) -> bool {
    (qr != kr || qc != kc) && (
        qr == kr || qc == kc || abs_val(qr - kr) == abs_val(qc - kc)
    )
}

pub open spec fn step_count(qr: int, qc: int, kr: int, kc: int) -> int {
    if abs_val(qr - kr) >= abs_val(qc - kc) {
        abs_val(qr - kr)
    } else {
        abs_val(qc - kc)
    }
}

pub open spec fn is_blocker(queens: Seq<Vec<i32>>, qi: int, qj: int, kr: int, kc: int) -> bool
    recommends
        0 <= qi < queens.len(),
        0 <= qj < queens.len(),
        queens[qi].len() == 2,
        queens[qj].len() == 2,
{
    let qr = queens[qi][0] as int;
    let qc = queens[qi][1] as int;
    let br = queens[qj][0] as int;
    let bc = queens[qj][1] as int;
    on_line(br, bc, kr, kc) &&
    sign_val(br - kr) == sign_val(qr - kr) &&
    sign_val(bc - kc) == sign_val(qc - kc) &&
    step_count(br, bc, kr, kc) < step_count(qr, qc, kr, kc)
}

pub open spec fn directly_attacks(queens: Seq<Vec<i32>>, qi: int, kr: int, kc: int) -> bool
    recommends
        0 <= qi < queens.len(),
        queens[qi].len() == 2,
        forall |j: int| 0 <= j < queens.len() ==> queens[j].len() == 2,
{
    on_line(queens[qi][0] as int, queens[qi][1] as int, kr, kc) &&
    forall |qj: int| 0 <= qj < queens.len() && qj != qi ==>
        !is_blocker(queens, qi, qj, kr, kc)
}

pub open spec fn in_result_range(result: Seq<Vec<i32>>, i: int) -> bool {
    0 <= i < result.len()
}

impl Solution {
    pub fn queens_attackthe_king(queens: Vec<Vec<i32>>, king: Vec<i32>) -> (result: Vec<Vec<i32>>)
        requires
            1 <= queens.len() < 64,
            forall |i: int| 0 <= i < queens.len() ==> (#[trigger] queens[i]).len() == 2,
            forall |i: int| 0 <= i < queens.len() ==>
                0 <= (#[trigger] queens[i])[0] < 8 && 0 <= queens[i][1] < 8,
            forall |i: int, j: int| 0 <= i < j < queens.len() ==>
                !(queens[i][0] == queens[j][0] && queens[i][1] == queens[j][1]),
            king.len() == 2,
            0 <= king[0] < 8,
            0 <= king[1] < 8,
            forall |i: int| 0 <= i < queens.len() ==>
                !(queens[i][0] == king[0] && queens[i][1] == king[1]),
        ensures
            forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]).len() == 2,
            forall |i: int| 0 <= i < result.len() ==>
                0 <= (#[trigger] result[i])[0] < 8 && 0 <= result[i][1] < 8,
            forall |i: int| #[trigger] in_result_range(result@, i) && 0 <= i < result.len() ==> (
                exists |qi: int| 0 <= qi < queens.len() &&
                    result[i][0] == queens[qi][0] &&
                    result[i][1] == queens[qi][1] &&
                    directly_attacks(queens@, qi, king[0] as int, king[1] as int)
            ),
            forall |qi: int| 0 <= qi < queens.len() &&
                (#[trigger] directly_attacks(queens@, qi, king[0] as int, king[1] as int)) ==> (
                exists |i: int| 0 <= i < result.len() &&
                    result[i][0] == queens[qi][0] && result[i][1] == queens[qi][1]
            ),
    {
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

}
