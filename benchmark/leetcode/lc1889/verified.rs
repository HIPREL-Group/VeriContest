use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_box_upto(boxes_j: Seq<i32>, pkg: i32, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::min_box_upto(boxes_j, pkg, end - 1);
            let cur = boxes_j[end - 1] as int;
            if cur >= pkg as int {
                if prev == -1 || cur <= prev { cur } else { prev }
            } else {
                prev
            }
        }
    }

    pub open spec fn can_fit_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> bool
        decreases end
    {
        if end <= 0 {
            true
        } else {
            Self::can_fit_upto(packages, boxes_j, end - 1)
                && Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) >= packages[end - 1] as int
        }
    }

    pub open spec fn waste_upto(packages: Seq<i32>, boxes_j: Seq<i32>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            (Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int) - packages[end - 1] as int)
                + Self::waste_upto(packages, boxes_j, end - 1)
        }
    }

    pub open spec fn best_waste_upto(packages: Seq<i32>, boxes: Seq<Vec<i32>>, end: int) -> int
        decreases end
    {
        if end <= 0 {
            -1
        } else {
            let prev = Self::best_waste_upto(packages, boxes, end - 1);
            let boxes_j = boxes[end - 1]@;
            let n = packages.len() as int;
            if Self::can_fit_upto(packages, boxes_j, n) {
                let w = Self::waste_upto(packages, boxes_j, n);
                if prev == -1 || w < prev { w } else { prev }
            } else {
                prev
            }
        }
    }

    proof fn lemma_min_box_upto_bounds(boxes_j: Seq<i32>, pkg: i32, end: int)
        requires
            end <= boxes_j.len(),
            forall |k: int| 0 <= k < boxes_j.len() ==> 1 <= #[trigger] boxes_j[k] <= 100_000,
        ensures
            Self::min_box_upto(boxes_j, pkg, end) == -1
                || (1 <= Self::min_box_upto(boxes_j, pkg, end) <= 100_000),
        decreases end
    {
        if end <= 0 {
        } else {
            Self::lemma_min_box_upto_bounds(boxes_j, pkg, end - 1);
        }
    }

    proof fn lemma_min_box_upto_ge_pkg(boxes_j: Seq<i32>, pkg: i32, end: int)
        requires
            end <= boxes_j.len(),
        ensures
            Self::min_box_upto(boxes_j, pkg, end) == -1
                || Self::min_box_upto(boxes_j, pkg, end) >= pkg as int,
        decreases end
    {
        if end <= 0 {
        } else {
            Self::lemma_min_box_upto_ge_pkg(boxes_j, pkg, end - 1);
        }
    }

    proof fn lemma_waste_upto_bounds(packages: Seq<i32>, boxes_j: Seq<i32>, end: int)
        requires
            0 <= end <= packages.len(),
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            forall |k: int| 0 <= k < boxes_j.len() ==> 1 <= #[trigger] boxes_j[k] <= 100_000,
            Self::can_fit_upto(packages, boxes_j, end),
        ensures
            0 <= Self::waste_upto(packages, boxes_j, end) <= end * 100_000,
        decreases end
    {
        if end <= 0 {
        } else {
            Self::lemma_waste_upto_bounds(packages, boxes_j, end - 1);
            Self::lemma_min_box_upto_bounds(boxes_j, packages[end - 1], boxes_j.len() as int);
            let mb = Self::min_box_upto(boxes_j, packages[end - 1], boxes_j.len() as int);
            assert(mb >= packages[end - 1] as int);
            assert(mb <= 100_000);
            assert(mb - packages[end - 1] as int >= 0);
            assert(mb - packages[end - 1] as int <= 100_000) by(nonlinear_arith)
                requires mb <= 100_000, packages[end - 1] >= 1
            {}
        }
    }

    proof fn lemma_best_waste_upto_bounds(packages: Seq<i32>, boxes: Seq<Vec<i32>>, end: int)
        requires
            0 <= end <= boxes.len(),
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            forall |j: int| #![trigger boxes[j]] 0 <= j < boxes.len() ==> 1 <= boxes[j]@.len() <= 100_000,
            forall |j: int, k: int| 0 <= j < boxes.len() && 0 <= k < boxes[j]@.len()
                ==> 1 <= #[trigger] boxes[j]@[k] <= 100_000,
        ensures
            Self::best_waste_upto(packages, boxes, end) == -1
                || (0 <= Self::best_waste_upto(packages, boxes, end) <= (packages.len() as int) * 100_000),
        decreases end
    {
        if end <= 0 {
        } else {
            Self::lemma_best_waste_upto_bounds(packages, boxes, end - 1);
            let boxes_j = boxes[end - 1]@;
            let n = packages.len() as int;
            if Self::can_fit_upto(packages, boxes_j, n) {
                Self::lemma_waste_upto_bounds(packages, boxes_j, n);
            }
        }
    }

    pub fn min_wasted_space(packages: Vec<i32>, boxes: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= packages.len() <= 100_000,
            forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
            1 <= boxes.len() <= 100_000,
            forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
            forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
                ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
        ensures
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) == -1 ==> res == -1i32,
            Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) >= 0 ==>
                res == (Self::best_waste_upto(packages@, boxes@, boxes@.len() as int) % 1_000_000_007) as i32,
    {
        let n = packages.len();
        let m = boxes.len();
        let modulus: i64 = 1_000_000_007;
        let mut best: i64 = -1;
        let mut j: usize = 0;
        while j < m
            invariant
                n == packages.len(),
                m == boxes@.len(),
                1 <= n <= 100_000,
                1 <= m <= 100_000,
                0 <= j <= m,
                forall |ii: int| 0 <= ii < packages@.len() ==> 1 <= #[trigger] packages@[ii] <= 100_000,
                forall |jj: int| #![trigger boxes@[jj]] 0 <= jj < boxes@.len() ==> 1 <= boxes@[jj]@.len() <= 100_000,
                forall |jj: int, kk: int| 0 <= jj < boxes@.len() && 0 <= kk < boxes@[jj]@.len()
                    ==> 1 <= #[trigger] boxes@[jj]@[kk] <= 100_000,
                best as int == Self::best_waste_upto(packages@, boxes@, j as int),
                best == -1 || (0 <= best <= n as i64 * 100_000),
            decreases m - j
        {
            let bj_len = boxes[j].len();
            let ghost boxes_j_spec = boxes@[j as int]@;
            let mut can_fit: bool = true;
            let mut waste: i64 = 0;
            let mut i: usize = 0;
            let ghost mut waste_bound: int = 0;
            while i < n
                invariant
                    n == packages@.len(),
                    m == boxes@.len(),
                    0 <= j < m,
                    0 <= i <= n,
                    1 <= n <= 100_000,
                    boxes_j_spec == boxes@[j as int]@,
                    bj_len == boxes_j_spec.len(),
                    1 <= bj_len <= 100_000,
                    forall |ii: int| 0 <= ii < packages@.len() ==> 1 <= #[trigger] packages@[ii] <= 100_000,
                    forall |kk: int| 0 <= kk < boxes_j_spec.len() ==> 1 <= #[trigger] boxes_j_spec[kk] <= 100_000,
                    can_fit == Self::can_fit_upto(packages@, boxes_j_spec, i as int),
                    can_fit ==> waste as int == Self::waste_upto(packages@, boxes_j_spec, i as int),
                    can_fit ==> 0 <= waste <= waste_bound,
                    waste_bound == (i as int) * 100_000,
                decreases n - i
            {
                if can_fit {
                    let pkg: i64 = packages[i] as i64;
                    let mut min_box: i64 = -1;
                    let mut k: usize = 0;
                    while k < bj_len
                        invariant
                            0 <= j < m,
                            0 <= i < n,
                            n == packages@.len(),
                            m == boxes@.len(),
                            boxes_j_spec == boxes@[j as int]@,
                            bj_len == boxes_j_spec.len(),
                            1 <= bj_len <= 100_000,
                            0 <= k <= bj_len,
                            pkg == packages@[i as int] as i64,
                            1 <= pkg <= 100_000,
                            forall |kk: int| 0 <= kk < boxes_j_spec.len() ==> 1 <= #[trigger] boxes_j_spec[kk] <= 100_000,
                            min_box as int == Self::min_box_upto(boxes_j_spec, packages@[i as int], k as int),
                            min_box == -1 || (1 <= min_box <= 100_000),
                        decreases bj_len - k
                    {
                        let b: i64 = boxes[j][k] as i64;
                        if b >= pkg {
                            if min_box == -1 || b <= min_box {
                                min_box = b;
                            }
                        }
                        k = k + 1;
                    }
                    assert(min_box as int == Self::min_box_upto(boxes_j_spec, packages@[i as int], bj_len as int));
                    if min_box == -1 {
                        can_fit = false;
                    } else {
                        proof {
                            Self::lemma_min_box_upto_ge_pkg(boxes_j_spec, packages@[i as int], bj_len as int);
                            Self::lemma_min_box_upto_bounds(boxes_j_spec, packages@[i as int], bj_len as int);
                        }
                        waste = waste + min_box - pkg;
                    }
                }
                proof {
                    waste_bound = waste_bound + 100_000;
                    assert(can_fit == Self::can_fit_upto(packages@, boxes_j_spec, (i + 1) as int));
                    if can_fit {
                        assert(waste as int == Self::waste_upto(packages@, boxes_j_spec, (i + 1) as int));
                    }
                }
                i = i + 1;
            }
            if can_fit && (best == -1 || waste < best) {
                best = waste;
            }
            j = j + 1;
        }
        proof {
            Self::lemma_best_waste_upto_bounds(packages@, boxes@, m as int);
        }
        if best == -1 {
            -1
        } else {
            (best % modulus) as i32
        }
    }
}

}
