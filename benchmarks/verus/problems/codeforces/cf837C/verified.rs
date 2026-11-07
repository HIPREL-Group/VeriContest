use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn fits_oriented(w1: i32, h1: i32, w2: i32, h2: i32, a: i32, b: i32) -> bool {
    (w1 + w2 <= a && h1 <= b && h2 <= b) ||
    (h1 + h2 <= b && w1 <= a && w2 <= a)
}

pub open spec fn fits(x1: i32, y1: i32, x2: i32, y2: i32, a: i32, b: i32) -> bool {
    fits_oriented(x1, y1, x2, y2, a, b) ||
    fits_oriented(y1, x1, x2, y2, a, b) ||
    fits_oriented(x1, y1, y2, x2, a, b) ||
    fits_oriented(y1, x1, y2, x2, a, b)
}

pub open spec fn is_valid_pair(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i: int, j: int) -> bool {
    0 <= i && i < x.len() && 0 <= j && j < x.len() && i != j &&
    fits(x[i], y[i], x[j], y[j], a, b)
}

pub open spec fn area(x: Seq<i32>, y: Seq<i32>, i: int, j: int) -> i32 {
    (x[i] as int * y[i] as int + x[j] as int * y[j] as int) as i32
}

pub open spec fn is_correct_ans(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, ans: i32) -> bool {
    (forall|i: int, j: int| #[trigger] is_valid_pair(x, y, a, b, i, j) ==> area(x, y, i, j) <= ans)
    &&
    (
        (ans == 0 && (forall|i: int, j: int| !is_valid_pair(x, y, a, b, i, j)))
        ||
        (exists|i: int, j: int| #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
    )
}

pub open spec fn ans_is_upper_bound(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32) -> bool {
    forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) ==> area(x, y, i, j) <= ans
}

pub open spec fn ans_witness_exists(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32) -> bool {
    (ans == 0 && (forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() ==> !#[trigger] is_valid_pair(x, y, a, b, i, j)))
    ||
    (exists|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
}

pub open spec fn inner_ans_is_upper_bound(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, j_bound: int, ans: i32) -> bool {
    ans_is_upper_bound(x, y, a, b, i_bound, ans) &&
    (forall|j: int| i_bound < j && j < j_bound ==> 
        (#[trigger] is_valid_pair(x, y, a, b, i_bound, j) ==> area(x, y, i_bound, j) <= ans))
}

pub open spec fn inner_ans_witness_exists(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, j_bound: int, ans: i32) -> bool {
    (ans == 0 && 
        (forall|i: int, j: int| 0 <= i && i < i_bound && i < j && j < x.len() ==> !#[trigger] is_valid_pair(x, y, a, b, i, j)) &&
        (forall|j: int| i_bound < j && j < j_bound ==> !#[trigger] is_valid_pair(x, y, a, b, i_bound, j)))
    ||
    (exists|i: int, j: int| 
        ((0 <= i && i < i_bound && i < j && j < x.len()) || (i == i_bound && i_bound < j && j < j_bound)) &&
        #[trigger] is_valid_pair(x, y, a, b, i, j) && area(x, y, i, j) == ans)
}

pub struct Solution;

impl Solution {
    pub fn fits_oriented(w1: i32, h1: i32, w2: i32, h2: i32, a: i32, b: i32) -> (res: bool)
        requires 0 <= w1 && w1 <= 100, 0 <= h1 && h1 <= 100, 0 <= w2 && w2 <= 100, 0 <= h2 && h2 <= 100
        ensures res == crate::fits_oriented(w1, h1, w2, h2, a, b)
    {
        (w1 + w2 <= a && h1 <= b && h2 <= b) ||
        (h1 + h2 <= b && w1 <= a && w2 <= a)
    }

    pub fn fits(x1: i32, y1: i32, x2: i32, y2: i32, a: i32, b: i32) -> (res: bool)
        requires 0 <= x1 && x1 <= 100, 0 <= y1 && y1 <= 100, 0 <= x2 && x2 <= 100, 0 <= y2 && y2 <= 100
        ensures res == crate::fits(x1, y1, x2, y2, a, b)
    {
        Solution::fits_oriented(x1, y1, x2, y2, a, b) ||
        Solution::fits_oriented(y1, x1, x2, y2, a, b) ||
        Solution::fits_oriented(x1, y1, y2, x2, a, b) ||
        Solution::fits_oriented(y1, x1, y2, x2, a, b)
    }

    proof fn lemma_symmetry(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i: int, j: int)
        requires 0 <= i && i < x.len() && 0 <= j && j < x.len() && i != j
        ensures
            is_valid_pair(x, y, a, b, i, j) == is_valid_pair(x, y, a, b, j, i),
            area(x, y, i, j) == area(x, y, j, i)
    {
    }

    proof fn lemma_apply_upper_bound(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32, i: int, j: int)
        requires
            ans_is_upper_bound(x, y, a, b, i_bound, ans),
            0 <= i && i < i_bound && i < j && j < x.len(),
            is_valid_pair(x, y, a, b, i, j)
        ensures
            area(x, y, i, j) <= ans
    {
    }

    proof fn lemma_ans_zero_implies_no_valid_pair(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, ans: i32, i: int, j: int)
        requires
            ans == 0,
            ans_witness_exists(x, y, a, b, i_bound, ans),
            0 <= i && i < i_bound && i < j && j < x.len(),
            x.len() == y.len(),
            forall|k: int| 0 <= k && k < x.len() ==> 1 <= x[k] && x[k] <= 100,
            forall|k: int| 0 <= k && k < y.len() ==> 1 <= y[k] && y[k] <= 100
        ensures
            !is_valid_pair(x, y, a, b, i, j)
    {
        if exists|i_idx: int, j_idx: int| 0 <= i_idx && i_idx < i_bound && i_idx < j_idx && j_idx < x.len() &&
            #[trigger] is_valid_pair(x, y, a, b, i_idx, j_idx) && area(x, y, i_idx, j_idx) == 0
        {
            let (i_wit, j_wit): (int, int) = choose|i_idx: int, j_idx: int| 0 <= i_idx && i_idx < i_bound && i_idx < j_idx && j_idx < x.len() &&
                #[trigger] is_valid_pair(x, y, a, b, i_idx, j_idx) && area(x, y, i_idx, j_idx) == 0;
            let rx = x[i_wit] as int; let ry = y[i_wit] as int; let sx = x[j_wit] as int; let sy = y[j_wit] as int;
            assert(1 <= rx * ry && rx * ry <= 10000) by (nonlinear_arith) requires 1 <= rx && rx <= 100, 1 <= ry && ry <= 100;
            assert(1 <= sx * sy && sx * sy <= 10000) by (nonlinear_arith) requires 1 <= sx && sx <= 100, 1 <= sy && sy <= 100;
        }
    }

    proof fn lemma_upper_bound_monotonic(x: Seq<i32>, y: Seq<i32>, a: i32, b: i32, i_bound: int, j_bound: int, old_ans: i32, new_ans: i32)
        requires 
            inner_ans_is_upper_bound(x, y, a, b, i_bound, j_bound, old_ans),
            old_ans <= new_ans
        ensures
            inner_ans_is_upper_bound(x, y, a, b, i_bound, j_bound, new_ans)
    {
    }

    pub fn two_seals(n: usize, a: i32, b: i32, x: Vec<i32>, y: Vec<i32>) -> (ans: i32)
        requires
            n == x.len(),
            n == y.len(),
            1 <= n && n <= 100,
            1 <= a && a <= 100,
            1 <= b && b <= 100,
            forall|i: int| 0 <= i && i < n ==> 1 <= x@[i] && x@[i] <= 100,
            forall|i: int| 0 <= i && i < n ==> 1 <= y@[i] && y@[i] <= 100,
        ensures
            is_correct_ans(x@, y@, a, b, ans),
    {
        let mut ans: i32 = 0;
        let mut i = 0;
        while i < n 
            invariant
                0 <= i && i <= n,
                n == x.len(),
                n == y.len(),
                1 <= n && n <= 100,
                1 <= a && a <= 100,
                1 <= b && b <= 100,
                forall|k: int| 0 <= k && k < n ==> 1 <= x@[k] && x@[k] <= 100,
                forall|k: int| 0 <= k && k < n ==> 1 <= y@[k] && y@[k] <= 100,
                ans_is_upper_bound(x@, y@, a, b, i as int, ans),
                ans_witness_exists(x@, y@, a, b, i as int, ans),
            decreases n - i
        {
            let mut j = i + 1;
            while j < n
                invariant
                    0 <= i && i < n,
                    i + 1 <= j && j <= n,
                    n == x.len(),
                    n == y.len(),
                    1 <= n && n <= 100,
                    1 <= a && a <= 100,
                    1 <= b && b <= 100,
                    forall|k: int| 0 <= k && k < n ==> 1 <= x@[k] && x@[k] <= 100,
                    forall|k: int| 0 <= k && k < n ==> 1 <= y@[k] && y@[k] <= 100,
                    inner_ans_is_upper_bound(x@, y@, a, b, i as int, j as int, ans),
                    inner_ans_witness_exists(x@, y@, a, b, i as int, j as int, ans),
                decreases n - j
            {
                let is_fit = Solution::fits(x[i], y[i], x[j], y[j], a, b);
                proof {
                    assert(is_fit == fits(x@[i as int], y@[i as int], x@[j as int], y@[j as int], a, b));
                    assert(is_fit == is_valid_pair(x@, y@, a, b, i as int, j as int));
                }
                if is_fit {
                    let xi = x[i]; let yi = y[i]; let xj = x[j]; let yj = y[j];
                    proof {
                        assert(1 <= xi as int * yi as int && xi as int * yi as int <= 10000) by (nonlinear_arith) requires 1 <= xi as int && xi as int <= 100, 1 <= yi as int && yi as int <= 100;
                        assert(1 <= xj as int * yj as int && xj as int * yj as int <= 10000) by (nonlinear_arith) requires 1 <= xj as int && xj as int <= 100, 1 <= yj as int && yj as int <= 100;
                        assert(xi as int * yi as int + xj as int * yj as int <= 20000);
                        assert(xi as int * yi as int + xj as int * yj as int >= 2);
                    }
                    let area_val: i32 = xi * yi + xj * yj;
                    if area_val > ans {
                        proof {
                            Self::lemma_upper_bound_monotonic(x@, y@, a, b, i as int, j as int, ans, area_val);
                        }
                        ans = area_val;
                        proof {
                            assert(inner_ans_witness_exists(x@, y@, a, b, i as int, j as int + 1, ans));
                        }
                    } else {
                        proof {
                            assert(inner_ans_witness_exists(x@, y@, a, b, i as int, j as int + 1, ans));
                        }
                    }
                } else {
                    proof {
                        assert(inner_ans_witness_exists(x@, y@, a, b, i as int, j as int + 1, ans));
                    }
                }
                j += 1;
            }
            i += 1;
        }

        proof {
            assert forall|i_idx: int, j_idx: int| is_valid_pair(x@, y@, a, b, i_idx, j_idx) implies area(x@, y@, i_idx, j_idx) <= ans as int by {
                if 0 <= i_idx && i_idx < n && 0 <= j_idx && j_idx < n && i_idx != j_idx {
                    if i_idx < j_idx {
                        Self::lemma_apply_upper_bound(x@, y@, a, b, n as int, ans, i_idx, j_idx);
                    } else if i_idx > j_idx {
                        Self::lemma_symmetry(x@, y@, a, b, i_idx, j_idx);
                        Self::lemma_apply_upper_bound(x@, y@, a, b, n as int, ans, j_idx, i_idx);
                    }
                }
            }

            if ans == 0 {
                assert forall|i_idx: int, j_idx: int| !is_valid_pair(x@, y@, a, b, i_idx, j_idx) by {
                    if 0 <= i_idx && i_idx < n && 0 <= j_idx && j_idx < n && i_idx != j_idx {
                        if i_idx < j_idx {
                            Self::lemma_ans_zero_implies_no_valid_pair(x@, y@, a, b, n as int, ans, i_idx, j_idx);
                        } else {
                            Self::lemma_ans_zero_implies_no_valid_pair(x@, y@, a, b, n as int, ans, j_idx, i_idx);
                            Self::lemma_symmetry(x@, y@, a, b, i_idx, j_idx);
                        }
                    } else {
                        
                        assert(!is_valid_pair(x@, y@, a, b, i_idx, j_idx));
                    }
                }
            } else {
                assert(ans_witness_exists(x@, y@, a, b, n as int, ans));
            }
        }
        ans
    }
}

}
