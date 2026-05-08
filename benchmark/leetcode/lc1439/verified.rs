use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_sums(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int) -> nat
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
        if remaining >= 0 { 1 } else { 0 }
    } else if row < 0 || col >= mat[row].len() as int {
        0
    } else {
        count_sums(mat, row + 1, 0, remaining - mat[row][col] as int) +
        count_sums(mat, row, col + 1, remaining)
    }
}

pub open spec fn total_combos(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 1 }
    else { mat[row].len() as int * total_combos(mat, row + 1) }
}

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn max_sum(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 0 }
    else { mat[row][mat[row].len() - 1] as int + max_sum(mat, row + 1) }
}

proof fn count_sums_zero_neg(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int)
    requires
        remaining < 0,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            #[trigger] mat[i][j] >= 1,
        0 <= row <= mat.len(),
        row < mat.len() ==> 0 <= col <= mat[row].len(),
    ensures
        count_sums(mat, row, col, remaining) == 0,
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
    } else if col >= mat[row].len() as int {
    } else {
        assert(mat[row][col] >= 1);
        count_sums_zero_neg(mat, row + 1, 0, remaining - mat[row][col] as int);
        count_sums_zero_neg(mat, row, col + 1, remaining);
    }
}

proof fn count_sums_zero_sorted(mat: Seq<Vec<i32>>, row: int, col: int, remaining: int)
    requires
        0 <= row < mat.len(),
        0 <= col < mat[row].len(),
        remaining < mat[row][col] as int,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            #[trigger] mat[i][j] >= 1,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1,
    ensures
        count_sums(mat, row, col, remaining) == 0,
    decreases mat[row].len() - col
{
    count_sums_zero_neg(mat, row + 1, 0, remaining - mat[row][col] as int);
    if col + 1 < mat[row].len() as int {
        assert(mat[row][col] <= mat[row][col + 1]);
        count_sums_zero_sorted(mat, row, col + 1, remaining);
    }
    assert(count_sums(mat, row + 1, 0, remaining - mat[row][col] as int) == 0nat);
    assert(count_sums(mat, row, col + 1, remaining) == 0nat);
}

proof fn count_sums_monotone(mat: Seq<Vec<i32>>, row: int, col: int, r1: int, r2: int)
    requires
        r1 <= r2,
        0 <= row <= mat.len(),
        row < mat.len() ==> 0 <= col <= mat[row].len(),
    ensures
        count_sums(mat, row, col, r1) <= count_sums(mat, row, col, r2),
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
    } else if col >= mat[row].len() as int {
    } else {
        count_sums_monotone(mat, row + 1, 0, r1 - mat[row][col] as int, r2 - mat[row][col] as int);
        count_sums_monotone(mat, row, col + 1, r1, r2);
    }
}

proof fn max_sum_bound(mat: Seq<Vec<i32>>, row: int)
    requires
        0 <= row <= mat.len(),
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            #[trigger] mat[i][j] <= 5000,
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1,
    ensures
        max_sum(mat, row) <= (mat.len() as int - row) * 5000,
    decreases mat.len() - row
{
    if row >= mat.len() as int {
    } else {
        max_sum_bound(mat, row + 1);
        assert(mat[row][mat[row].len() - 1] <= 5000);
        assert((mat.len() as int - row) * 5000 == 5000 + (mat.len() as int - (row + 1)) * 5000) by(nonlinear_arith)
            requires mat.len() as int - row >= 1;
    }
}

proof fn sorted_row_transitive(mat: Seq<Vec<i32>>, row: int, lo: int, hi: int)
    requires
        0 <= row < mat.len(),
        0 <= lo <= hi < mat[row].len(),
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
    ensures
        mat[row][lo] <= mat[row][hi],
    decreases hi - lo
{
    if lo == hi {
    } else {
        sorted_row_transitive(mat, row, lo, hi - 1);
        assert(mat[row][hi - 1] <= mat[row][hi]);
    }
}

proof fn total_combos_positive(mat: Seq<Vec<i32>>, row: int)
    requires
        0 <= row <= mat.len(),
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1,
    ensures
        total_combos(mat, row) >= 1,
    decreases mat.len() - row
{
    if row >= mat.len() as int {
    } else {
        total_combos_positive(mat, row + 1);
        assert(mat[row].len() >= 1);
        assert(mat[row].len() as int * total_combos(mat, row + 1) >= 1) by(nonlinear_arith)
            requires mat[row].len() as int >= 1, total_combos(mat, row + 1) >= 1;
    }
}

proof fn count_at_max_geq_combos(mat: Seq<Vec<i32>>, row: int, col: int)
    requires
        0 <= row <= mat.len(),
        row < mat.len() ==> 0 <= col <= mat[row].len(),
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
            1 <= #[trigger] mat[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
            #[trigger] mat[i][j] <= mat[i][j + 1],
        forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1,
    ensures
        row >= mat.len() as int ==> count_sums(mat, row, col, max_sum(mat, row)) >= 1,
        row < mat.len() as int && col >= mat[row].len() as int ==> count_sums(mat, row, col, max_sum(mat, row)) == 0,
        row < mat.len() as int && col < mat[row].len() as int ==>
            count_sums(mat, row, col, max_sum(mat, row)) as int >=
                (mat[row].len() as int - col) * total_combos(mat, row + 1),
    decreases mat.len() - row, (if 0 <= row < mat.len() as int { mat[row].len() - col } else { 0 })
{
    if row >= mat.len() as int {
    } else if col >= mat[row].len() as int {
    } else {
        let last_idx = mat[row].len() as int - 1;
        sorted_row_transitive(mat, row, col, last_idx);

        let ghost rem_sub = max_sum(mat, row) - mat[row][col] as int;
        assert(rem_sub >= max_sum(mat, row + 1)) by {
            assert(max_sum(mat, row) == mat[row][last_idx] as int + max_sum(mat, row + 1));
            assert(mat[row][col] <= mat[row][last_idx]);
        };

        
        count_at_max_geq_combos(mat, row + 1, 0);
        count_sums_monotone(mat, row + 1, 0, max_sum(mat, row + 1), rem_sub);

        
        if row + 1 < mat.len() as int {
            assert(count_sums(mat, row + 1, 0, max_sum(mat, row + 1)) as int >=
                mat[row + 1].len() as int * total_combos(mat, row + 2));
            assert(total_combos(mat, row + 1) == mat[row + 1].len() as int * total_combos(mat, row + 2));
        } else {
            assert(count_sums(mat, row + 1, 0, max_sum(mat, row + 1)) >= 1nat);
            assert(total_combos(mat, row + 1) == 1int);
        }
        assert(count_sums(mat, row + 1, 0, rem_sub) as int >= total_combos(mat, row + 1));

        
        count_at_max_geq_combos(mat, row, col + 1);

        
        
        
        
        

        total_combos_positive(mat, row + 1);

        if col + 1 < mat[row].len() as int {
            assert(count_sums(mat, row, col + 1, max_sum(mat, row)) as int >=
                (mat[row].len() as int - col - 1) * total_combos(mat, row + 1));
        }

        let ghost a = count_sums(mat, row + 1, 0, rem_sub) as int;
        let ghost b = count_sums(mat, row, col + 1, max_sum(mat, row)) as int;
        let ghost tc = total_combos(mat, row + 1);
        let ghost ncol = mat[row].len() as int - col;

        assert(a >= tc);
        if col + 1 < mat[row].len() as int {
            assert(b >= (ncol - 1) * tc);
        } else {
            assert(b == 0);
            assert(ncol == 1);
        }
        assert(count_sums(mat, row, col, max_sum(mat, row)) as int == a + b);
        assert(a + b >= ncol * tc) by(nonlinear_arith)
            requires a >= tc, tc >= 1, ncol >= 1,
                     ncol > 1 ==> b >= (ncol - 1) * tc,
                     ncol == 1 ==> b >= 0;
    }
}

impl Solution {
    fn count_leq(mat: &Vec<Vec<i32>>, row: usize, col: usize, remaining: i32, cap: i32) -> (result: i32)
        requires
            cap >= 0,
            cap <= 200,
            row <= mat.len(),
            row < mat.len() ==> col <= mat[row as int].len(),
            mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
        ensures
            0 <= result <= cap,
            result as int == min_spec(count_sums(mat@, row as int, col as int, remaining as int) as int, cap as int),
        decreases mat.len() - row, (if (row as int) < mat.len() as int { mat[row as int].len() - col } else { 0 })
    {
        if row >= mat.len() {
            if remaining >= 0 && cap >= 1 { return 1; } else { return 0; }
        }
        if col >= mat[row].len() {
            return 0;
        }
        if remaining < mat[row][col] {
            proof {
                count_sums_zero_sorted(mat@, row as int, col as int, remaining as int);
            }
            return 0;
        }
        let sub = Self::count_leq(mat, row + 1, 0, remaining - mat[row][col], cap);
        if sub >= cap {
            proof {
                let ghost a = count_sums(mat@, (row + 1) as int, 0int, remaining as int - mat@[row as int][col as int] as int) as int;
                let ghost b = count_sums(mat@, row as int, (col + 1) as int, remaining as int) as int;
            }
            return cap;
        }
        let rest = Self::count_leq(mat, row, col + 1, remaining, cap - sub);
        let total = sub + rest;
        proof {
            let ghost a = count_sums(mat@, (row + 1) as int, 0int, remaining as int - mat@[row as int][col as int] as int) as int;
            let ghost b = count_sums(mat@, row as int, (col + 1) as int, remaining as int) as int;
            let ghost c = cap as int;
            assert(sub as int == a);
            assert(rest as int == min_spec(b, c - a));
            assert(count_sums(mat@, row as int, col as int, remaining as int) as int == a + b);
            if b >= c - a {
                assert(rest as int == c - a);
                assert(total as int == c);
                assert(a + b >= c);
                assert(min_spec(a + b, c) == c);
            } else {
                assert(rest as int == b);
                assert(total as int == a + b);
                assert(a + b < c);
                assert(min_spec(a + b, c) == a + b);
            }
        }
        if total >= cap { cap } else { total }
    }

    pub fn kth_smallest(mat: Vec<Vec<i32>>, k: i32) -> (result: i32)
        requires
            1 <= mat.len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == mat[0].len(),
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
            1 <= k <= 200,
            k as int <= total_combos(mat@, 0),
        ensures
            count_sums(mat@, 0, 0, result as int) >= k as int,
            count_sums(mat@, 0, 0, result as int - 1) < k as int,
    {
        let mut lo: i32 = 0;
        let mut hi: i32 = (mat.len() as i32) * 5000;
        proof {
            count_sums_zero_neg(mat@, 0, 0, -1);
            max_sum_bound(mat@, 0);
            count_at_max_geq_combos(mat@, 0, 0);
            total_combos_positive(mat@, 0);
            count_sums_monotone(mat@, 0, 0, max_sum(mat@, 0), hi as int);
        }
        while lo < hi
            invariant
                count_sums(mat@, 0, 0, lo as int - 1) < k as int,
                count_sums(mat@, 0, 0, hi as int) >= k as int,
                lo <= hi,
                0 <= lo,
                hi <= (mat.len() as int) * 5000,
                mat.len() <= 40,
                forall|i: int| 0 <= i < mat.len() ==> #[trigger] mat[i].len() >= 1 && mat[i].len() <= 40,
                forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                    1 <= #[trigger] mat[i][j] <= 5000,
                forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                    #[trigger] mat[i][j] <= mat[i][j + 1],
                1 <= k <= 200,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let cnt = Self::count_leq(&mat, 0, 0, mid, k);
            if cnt >= k {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        
        lo
    }
}

}
