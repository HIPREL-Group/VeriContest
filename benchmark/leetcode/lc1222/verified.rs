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

#[verifier::opaque]
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
        let ghost mut qi_map: Seq<int> = Seq::empty();
        let ghost mut ri_map: Seq<int> = Seq::new(queens.len() as nat, |_q: int| -1int);
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == queens.len(),
                1 <= queens.len() < 64,
                forall |idx: int| 0 <= idx < queens.len() ==> (#[trigger] queens[idx]).len() == 2,
                forall |idx: int| 0 <= idx < queens.len() ==>
                    0 <= (#[trigger] queens[idx])[0] < 8 && 0 <= queens[idx][1] < 8,
                forall |idx: int, jdx: int| 0 <= idx < jdx < queens.len() ==>
                    !(queens[idx][0] == queens[jdx][0] && queens[idx][1] == queens[jdx][1]),
                king.len() == 2,
                kr == king[0],
                kc == king[1],
                0 <= kr < 8,
                0 <= kc < 8,
                forall |idx: int| 0 <= idx < queens.len() ==>
                    !(queens[idx][0] == king[0] && queens[idx][1] == king[1]),
                forall |ri: int| 0 <= ri < result.len() ==> (#[trigger] result[ri]).len() == 2,
                forall |ri: int| 0 <= ri < result.len() ==>
                    0 <= (#[trigger] result[ri])[0] < 8 && 0 <= result[ri][1] < 8,
                qi_map.len() == result.len(),
                forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() ==> (
                    0 <= qi_map[ri] < queens.len() &&
                    result[ri][0] == queens[qi_map[ri] as int][0] &&
                    result[ri][1] == queens[qi_map[ri] as int][1] &&
                    directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                ),
                
                ri_map.len() == queens.len(),
                forall |qi: int| #![trigger ri_map[qi]] 0 <= qi < i as int &&
                    directly_attacks(queens@, qi, king[0] as int, king[1] as int) ==> (
                    0 <= ri_map[qi] < result.len() as int &&
                    result[ri_map[qi]][0] == queens[qi][0] &&
                    result[ri_map[qi]][1] == queens[qi][1]
                ),
            decreases n - i,
        {
            let qr = queens[i][0];
            let qc = queens[i][1];
            let dr: i32 = if qr > kr { qr - kr } else { kr - qr };
            let dc: i32 = if qc > kc { qc - kc } else { kc - qc };
            proof {
                assert(dr as int == abs_val(qr as int - kr as int));
                assert(dc as int == abs_val(qc as int - kc as int));
            }
            let on_line_check: bool = (qr == kr || qc == kc || dr == dc) && (qr != kr || qc != kc);
            proof {
                assert(on_line_check == on_line(qr as int, qc as int, kr as int, kc as int));
            }
            let ghost result_snap = result@;
            let ghost qi_map_snap = qi_map;
            let ghost ri_map_snap = ri_map;
            if on_line_check {
                let sr_q: i32 = if qr > kr { 1 } else if qr < kr { -1 } else { 0 };
                let sc_q: i32 = if qc > kc { 1 } else if qc < kc { -1 } else { 0 };
                let q_dist: i32 = if dr >= dc { dr } else { dc };
                proof {
                    assert(sr_q as int == sign_val(qr as int - kr as int));
                    assert(sc_q as int == sign_val(qc as int - kc as int));
                    assert(q_dist as int == step_count(qr as int, qc as int, kr as int, kc as int));
                }
                let mut blocked: bool = false;
                let mut j: usize = 0;
                while j < n
                    invariant
                        0 <= j <= n,
                        n == queens.len(),
                        0 <= i < n,
                        1 <= queens.len() < 64,
                        forall |idx: int| 0 <= idx < queens.len() ==> (#[trigger] queens[idx]).len() == 2,
                        forall |idx: int| 0 <= idx < queens.len() ==>
                            0 <= (#[trigger] queens[idx])[0] < 8 && 0 <= queens[idx][1] < 8,
                        king.len() == 2,
                        kr == king[0],
                        kc == king[1],
                        0 <= kr < 8,
                        0 <= kc < 8,
                        qr == queens[i as int][0],
                        qc == queens[i as int][1],
                        on_line(qr as int, qc as int, kr as int, kc as int),
                        dr as int == abs_val(qr as int - kr as int),
                        dc as int == abs_val(qc as int - kc as int),
                        sr_q as int == sign_val(qr as int - kr as int),
                        sc_q as int == sign_val(qc as int - kc as int),
                        q_dist as int == step_count(qr as int, qc as int, kr as int, kc as int),
                        blocked == (exists |k: int| 0 <= k < j as int && k != i as int &&
                            is_blocker(queens@, i as int, k, kr as int, kc as int)),
                        result@ == result_snap,
                        qi_map == qi_map_snap,
                        ri_map == ri_map_snap,
                    decreases n - j,
                {
                    if j != i {
                        let br = queens[j][0];
                        let bc = queens[j][1];
                        let bdr: i32 = if br > kr { br - kr } else { kr - br };
                        let bdc: i32 = if bc > kc { bc - kc } else { kc - bc };
                        let sr_b: i32 = if br > kr { 1 } else if br < kr { -1 } else { 0 };
                        let sc_b: i32 = if bc > kc { 1 } else if bc < kc { -1 } else { 0 };
                        let b_dist: i32 = if bdr >= bdc { bdr } else { bdc };
                        let b_on_line: bool = (br == kr || bc == kc || bdr == bdc) && (br != kr || bc != kc);
                        proof {
                            assert(bdr as int == abs_val(br as int - kr as int));
                            assert(bdc as int == abs_val(bc as int - kc as int));
                            assert(sr_b as int == sign_val(br as int - kr as int));
                            assert(sc_b as int == sign_val(bc as int - kc as int));
                            assert(b_dist as int == step_count(br as int, bc as int, kr as int, kc as int));
                            assert(b_on_line == on_line(br as int, bc as int, kr as int, kc as int));
                        }
                        let is_block: bool = b_on_line && sr_b == sr_q && sc_b == sc_q && b_dist < q_dist;
                        proof {
                            assert(is_block == is_blocker(queens@, i as int, j as int, kr as int, kc as int));
                        }
                        if is_block {
                            blocked = true;
                        }
                    }
                    j = j + 1;
                }
                
                proof {
                    assert(result@ == result_snap);
                    assert(qi_map == qi_map_snap);
                    assert(ri_map == ri_map_snap);
                    assert forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() implies (
                        0 <= qi_map[ri] < queens.len() &&
                        result[ri][0] == queens[qi_map[ri] as int][0] &&
                        result[ri][1] == queens[qi_map[ri] as int][1] &&
                        directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                    ) by {
                        assert(result[ri] == result_snap[ri]);
                        assert(qi_map[ri] == qi_map_snap[ri]);
                    };
                    assert forall |qi: int| #![trigger ri_map[qi]] 0 <= qi < i as int &&
                        directly_attacks(queens@, qi, king[0] as int, king[1] as int) implies (
                        0 <= ri_map[qi] < result.len() as int &&
                        result[ri_map[qi]][0] == queens[qi][0] &&
                        result[ri_map[qi]][1] == queens[qi][1]
                    ) by {
                        assert(ri_map[qi] == ri_map_snap[qi]);
                        assert(result[ri_map[qi]] == result_snap[ri_map[qi] as int]);
                    };
                }
                if !blocked {
                    proof {
                        reveal(directly_attacks);
                        assert(directly_attacks(queens@, i as int, kr as int, kc as int));
                    }
                    let ghost pre_len = result@.len();
                    let ghost old_result = result@;
                    let ghost old_qi_map = qi_map;
                    let ghost old_ri_map = ri_map;
                    let mut pair: Vec<i32> = Vec::new();
                    pair.push(qr);
                    pair.push(qc);
                    result.push(pair);
                    proof {
                        qi_map = qi_map.push(i as int);
                        ri_map = ri_map.update(i as int, pre_len as int);
                        assert(result@.len() == pre_len + 1);
                        assert(qi_map.len() == result.len());
                        assert(ri_map.len() == queens.len());
                        assert(result[pre_len as int].len() == 2);
                        assert(result[pre_len as int][0] == qr);
                        assert(result[pre_len as int][1] == qc);
                        assert(qr == queens[i as int][0]);
                        assert(qc == queens[i as int][1]);
                        
                        assert forall |ri: int| 0 <= ri < pre_len as int implies
                            (#[trigger] result[ri]) == old_result[ri] by {};
                        
                        assert forall |ri: int| 0 <= ri < result.len() implies (#[trigger] result[ri]).len() == 2 by {
                            if ri < pre_len as int {
                                assert(result[ri] == old_result[ri]);
                            }
                        };
                        
                        assert forall |ri: int| 0 <= ri < result.len() implies
                            0 <= (#[trigger] result[ri])[0] < 8 && 0 <= result[ri][1] < 8 by {
                            if ri < pre_len as int {
                                assert(result[ri] == old_result[ri]);
                            }
                        };
                        
                        assert forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() implies (
                            0 <= qi_map[ri] < queens.len() &&
                            result[ri][0] == queens[qi_map[ri] as int][0] &&
                            result[ri][1] == queens[qi_map[ri] as int][1] &&
                            directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                        ) by {
                            if ri == pre_len as int {
                                assert(qi_map[ri] == i as int);
                                assert(result[ri][0] == queens[i as int][0]);
                                assert(result[ri][1] == queens[i as int][1]);
                            } else {
                                assert(qi_map[ri] == old_qi_map[ri]);
                                assert(result[ri] == old_result[ri]);
                            }
                        };
                        
                        assert forall |qi: int| #![trigger ri_map[qi]] 0 <= qi < (i + 1) as int &&
                            directly_attacks(queens@, qi, king[0] as int, king[1] as int) implies (
                            0 <= ri_map[qi] < result.len() as int &&
                            result[ri_map[qi]][0] == queens[qi][0] &&
                            result[ri_map[qi]][1] == queens[qi][1]
                        ) by {
                            if qi == i as int {
                                assert(ri_map[qi] == pre_len as int);
                                assert(result[pre_len as int][0] == queens[i as int][0]);
                                assert(result[pre_len as int][1] == queens[i as int][1]);
                            } else {
                                assert(ri_map[qi] == old_ri_map[qi]);
                                assert(result[ri_map[qi]] == old_result[ri_map[qi] as int]);
                            }
                        };
                    }
                } else {
                    proof {
                        reveal(directly_attacks);
                        assert(!directly_attacks(queens@, i as int, kr as int, kc as int));
                    }
                }
            } else {
                proof {
                    reveal(directly_attacks);
                    assert(!on_line(qr as int, qc as int, kr as int, kc as int));
                    assert(!directly_attacks(queens@, i as int, kr as int, kc as int));
                    
                    assert forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() implies (
                        0 <= qi_map[ri] < queens.len() &&
                        result[ri][0] == queens[qi_map[ri] as int][0] &&
                        result[ri][1] == queens[qi_map[ri] as int][1] &&
                        directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                    ) by {
                        assert(result[ri] == result_snap[ri]);
                        assert(qi_map[ri] == qi_map_snap[ri]);
                    };
                    
                    assert forall |qi: int| #![trigger ri_map[qi]] 0 <= qi < i as int &&
                        directly_attacks(queens@, qi, king[0] as int, king[1] as int) implies (
                        0 <= ri_map[qi] < result.len() as int &&
                        result[ri_map[qi]][0] == queens[qi][0] &&
                        result[ri_map[qi]][1] == queens[qi][1]
                    ) by {
                        assert(ri_map[qi] == ri_map_snap[qi]);
                        assert(result[ri_map[qi]] == result_snap[ri_map[qi] as int]);
                    };
                }
            }
            
            proof {
                assert forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() implies (
                    0 <= qi_map[ri] < queens.len() &&
                    result[ri][0] == queens[qi_map[ri] as int][0] &&
                    result[ri][1] == queens[qi_map[ri] as int][1] &&
                    directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                ) by {
                    assert(result[ri].len() == 2);
                };
                assert forall |qi: int| #![trigger ri_map[qi]] 0 <= qi <= i as int &&
                    directly_attacks(queens@, qi, king[0] as int, king[1] as int) implies (
                    0 <= ri_map[qi] < result.len() as int &&
                    result[ri_map[qi]][0] == queens[qi][0] &&
                    result[ri_map[qi]][1] == queens[qi][1]
                ) by {};
            }
            i = i + 1;
            proof {
                assert(qi_map.len() == result.len());
                assert(ri_map.len() == queens.len());
                assert forall |ri: int| #![trigger qi_map[ri]] 0 <= ri < result.len() implies (
                    0 <= qi_map[ri] < queens.len() &&
                    result[ri][0] == queens[qi_map[ri] as int][0] &&
                    result[ri][1] == queens[qi_map[ri] as int][1] &&
                    directly_attacks(queens@, qi_map[ri], king[0] as int, king[1] as int)
                ) by {
                    assert(result[ri].len() == 2);
                };
                assert forall |qi: int| #![trigger ri_map[qi]] 0 <= qi < i as int &&
                    directly_attacks(queens@, qi, king[0] as int, king[1] as int) implies (
                    0 <= ri_map[qi] < result.len() as int &&
                    result[ri_map[qi]][0] == queens[qi][0] &&
                    result[ri_map[qi]][1] == queens[qi][1]
                ) by {};
            }
        }
        proof {
            
            assert forall |ri: int| #[trigger] in_result_range(result@, ri) && 0 <= ri < result.len() implies (
                exists |qi: int| 0 <= qi < queens.len() &&
                    result[ri][0] == queens[qi][0] &&
                    result[ri][1] == queens[qi][1] &&
                    directly_attacks(queens@, qi, king[0] as int, king[1] as int)
            ) by {
                let w = qi_map[ri];
                assert(0 <= w < queens.len() as int);
                assert(result[ri][0] == queens[w as int][0]);
                assert(result[ri][1] == queens[w as int][1]);
                assert(directly_attacks(queens@, w, king[0] as int, king[1] as int));
            };
            
            assert forall |qi: int| 0 <= qi < queens.len() &&
                (#[trigger] directly_attacks(queens@, qi, king[0] as int, king[1] as int)) implies (
                exists |ri: int| 0 <= ri < result.len() &&
                    result[ri][0] == queens[qi][0] && result[ri][1] == queens[qi][1]
            ) by {
                let w = ri_map[qi];
                assert(0 <= w < result.len() as int);
                assert(result[w][0] == queens[qi][0]);
                assert(result[w][1] == queens[qi][1]);
            };
        }
        result
    }
}

}
