use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

proof fn lemma_subrange_full<T>(s: Seq<T>)
    ensures
        s.subrange(0, s.len() as int) =~= s,
{
}

proof fn lemma_subrange_extend_one<T>(s: Seq<T>, end: int)
    requires
        0 <= end < s.len(),
    ensures
        s.subrange(0, end + 1) =~= s.subrange(0, end).push(s[end]),
{
    assert(s.subrange(0, end + 1).len() == s.subrange(0, end).push(s[end]).len());
    assert forall |i: int|
        0 <= i < s.subrange(0, end + 1).len()
        implies s.subrange(0, end + 1)[i] == s.subrange(0, end).push(s[end])[i]
    by {
        if i < end {
        } else {
            assert(i == end);
        }
    }
}

proof fn lemma_add_push<T>(s1: Seq<T>, s2: Seq<T>, x: T)
    ensures
        (s1 + s2).push(x) =~= s1 + s2.push(x),
{
    assert((s1 + s2).push(x).len() == (s1 + s2.push(x)).len());
    assert forall |i: int|
        0 <= i < (s1 + s2).push(x).len()
        implies (s1 + s2).push(x)[i] == (s1 + s2.push(x))[i]
    by {
        if i < s1.len() {
        } else if i < s1.len() + s2.len() {
            assert((s1 + s2)[i] == s2[i - s1.len()]);
            assert((s1 + s2.push(x))[i] == s2.push(x)[i - s1.len()]);
            assert(s2.push(x)[i - s1.len()] == s2[i - s1.len()]);
        } else {
            assert(i == s1.len() + s2.len());
            assert((s1 + s2).push(x)[i] == x);
            assert((s1 + s2.push(x))[i] == s2.push(x)[s2.len() as int]);
            assert(s2.push(x)[s2.len() as int] == x);
        }
    }
}

impl Solution {
    pub open spec fn total_diags(matrix: Seq<Vec<i32>>) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
    {
        matrix.len() + matrix[0].len() - 1
    }

    pub open spec fn diag_start_row(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        if d < matrix[0].len() {
            0
        } else {
            d - (matrix[0].len() - 1)
        }
    }

    pub open spec fn diag_end_row(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        if d < matrix.len() {
            d
        } else {
            matrix.len() - 1
        }
    }

    pub open spec fn diag_len(matrix: Seq<Vec<i32>>, d: int) -> int
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        Self::diag_end_row(matrix, d) - Self::diag_start_row(matrix, d) + 1
    }

    pub open spec fn diag_nth(matrix: Seq<Vec<i32>>, d: int, k: int) -> i32
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
            0 <= k < Self::diag_len(matrix, d),
    {
        let row = if d % 2 == 0 {
            Self::diag_end_row(matrix, d) - k
        } else {
            Self::diag_start_row(matrix, d) + k
        };
        matrix[row][d - row]
    }

    pub open spec fn diag_seq(matrix: Seq<Vec<i32>>, d: int) -> Seq<i32>
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
    {
        Seq::new(Self::diag_len(matrix, d) as nat, |k: int| Self::diag_nth(matrix, d, k))
    }

    pub open spec fn diagonal_prefix(matrix: Seq<Vec<i32>>, diag_count: int) -> Seq<i32>
        recommends
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= diag_count <= Self::total_diags(matrix),
        decreases diag_count,
    {
        if diag_count <= 0 {
            seq![]
        } else {
            Self::diagonal_prefix(matrix, diag_count - 1) + Self::diag_seq(matrix, diag_count - 1)
        }
    }

    proof fn lemma_diag_index_bounds(matrix: Seq<Vec<i32>>, d: int, k: int)
        requires
            1 <= matrix.len(),
            1 <= matrix[0].len(),
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            0 <= d < Self::total_diags(matrix),
            0 <= k < Self::diag_len(matrix, d),
        ensures
            0 <= if d % 2 == 0 { Self::diag_end_row(matrix, d) - k } else { Self::diag_start_row(matrix, d) + k } < matrix.len(),
            0 <= d - (if d % 2 == 0 { Self::diag_end_row(matrix, d) - k } else { Self::diag_start_row(matrix, d) + k }) < matrix[0].len(),
    {
        let start = Self::diag_start_row(matrix, d);
        let end = Self::diag_end_row(matrix, d);
        assert(Self::diag_len(matrix, d) == end - start + 1);
        assert(k <= end - start);
        assert(0 <= start);
        assert(end < matrix.len());
        if d < matrix[0].len() {
            assert(start == 0);
        } else {
            assert(start == d - (matrix[0].len() - 1));
        }
        if d < matrix.len() {
            assert(end == d);
        } else {
            assert(end == matrix.len() - 1);
        }
        if d % 2 == 0 {
            let row = end - k;
            assert(start <= row <= end);
            assert(0 <= row < matrix.len());
            assert(row <= d);
            assert(0 <= d - row);
            if d < matrix[0].len() {
                assert(d - row <= d);
                assert(d < matrix[0].len());
            } else {
                assert(d - start == matrix[0].len() - 1);
                assert(d - row <= d - start);
            }
        } else {
            let row = start + k;
            assert(start <= row <= end);
            assert(0 <= row < matrix.len());
            assert(row <= d);
            assert(0 <= d - row);
            if d < matrix[0].len() {
                assert(d - row <= d);
                assert(d < matrix[0].len());
            } else {
                assert(d - start == matrix[0].len() - 1);
                assert(d - row <= d - start);
            }
        }
    }

    pub fn find_diagonal_order(mat: Vec<Vec<i32>>) -> (result: Vec<i32>)
        requires
            1 <= mat.len() <= 10_000,
            1 <= mat[0].len() <= 10_000,
            forall |r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
            forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[0].len() ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
            mat.len() * mat[0].len() <= 10_000,
        ensures
            result@ == Self::diagonal_prefix(mat@, Self::total_diags(mat@)),
    {
        let rows = mat.len();
        let cols = mat[0].len();
        let total = rows + cols - 1;
        let mut result: Vec<i32> = Vec::new();
        let mut d: usize = 0;
        while d < total
            invariant
                rows == mat.len(),
                cols == mat[0].len(),
                total == rows + cols - 1,
                1 <= rows <= 10_000,
                1 <= cols <= 10_000,
                forall |r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == cols,
                forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < cols ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
                rows * cols <= 10_000,
                d <= total,
                result@ =~= Self::diagonal_prefix(mat@, d as int),
            decreases total - d,
        {
            proof {
                assert((d as int) < Self::total_diags(mat@));
            }
            let start = if d < cols { 0 } else { d - (cols - 1) };
            let end = if d < rows { d } else { rows - 1 };
            let len = end - start + 1;
            let mut k: usize = 0;
            while k < len
                invariant
                    rows == mat.len(),
                    cols == mat[0].len(),
                    total == rows + cols - 1,
                    1 <= rows <= 10_000,
                    1 <= cols <= 10_000,
                    forall |r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < mat.len() && 0 <= c < cols ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
                    rows * cols <= 10_000,
                    d < total,
                    start as int == Self::diag_start_row(mat@, d as int),
                    end as int == Self::diag_end_row(mat@, d as int),
                    len as int == Self::diag_len(mat@, d as int),
                    k <= len,
                    result@ =~= Self::diagonal_prefix(mat@, d as int) + Self::diag_seq(mat@, d as int).subrange(0, k as int),
                decreases len - k,
            {
                let row = if d % 2 == 0 { end - k } else { start + k };
                let col = d - row;
                proof {
                    Self::lemma_diag_index_bounds(mat@, d as int, k as int);
                    if d % 2 == 0 {
                        assert(row as int == Self::diag_end_row(mat@, d as int) - k as int);
                    } else {
                        assert(row as int == Self::diag_start_row(mat@, d as int) + k as int);
                    }
                    assert(col as int == d as int - row as int);
                    assert(row < rows);
                    assert(col < cols);
                    assert(mat[row as int].len() == cols);
                    assert(Self::diag_seq(mat@, d as int)[k as int] == Self::diag_nth(mat@, d as int, k as int));
                }
                let ghost prev = result@;
                let v = mat[row][col];
                result.push(v);
                proof {
                    assert(v == Self::diag_nth(mat@, d as int, k as int));
                    assert(prev =~= Self::diagonal_prefix(mat@, d as int) + Self::diag_seq(mat@, d as int).subrange(0, k as int));
                    assert(result@ =~= prev.push(v));
                    lemma_add_push(Self::diagonal_prefix(mat@, d as int), Self::diag_seq(mat@, d as int).subrange(0, k as int), v);
                    lemma_subrange_extend_one(Self::diag_seq(mat@, d as int), k as int);
                    assert(result@ =~= Self::diagonal_prefix(mat@, d as int) + Self::diag_seq(mat@, d as int).subrange(0, k as int).push(v));
                    assert(result@ =~= Self::diagonal_prefix(mat@, d as int) + Self::diag_seq(mat@, d as int).subrange(0, k as int + 1));
                }
                k = k + 1;
            }
            proof {
                assert(k == len);
                assert(len as int == Self::diag_seq(mat@, d as int).len());
                lemma_subrange_full(Self::diag_seq(mat@, d as int));
                assert(result@ =~= Self::diagonal_prefix(mat@, d as int) + Self::diag_seq(mat@, d as int));
                assert(result@ =~= Self::diagonal_prefix(mat@, d as int + 1));
            }
            d = d + 1;
        }
        result
    }
}

}
