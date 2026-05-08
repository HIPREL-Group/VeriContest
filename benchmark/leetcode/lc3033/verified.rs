use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;


pub open spec fn spec_col_max(matrix: Seq<Vec<i32>>, j: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        -1int
    } else if (matrix[k - 1][j] as int) > spec_col_max(matrix, j, k - 1) {
        matrix[k - 1][j] as int
    } else {
        spec_col_max(matrix, j, k - 1)
    }
}


pub open spec fn spec_answer_element(matrix: Seq<Vec<i32>>, i: int, j: int) -> int {
    if matrix[i][j] == -1 {
        spec_col_max(matrix, j, matrix.len() as int)
    } else {
        matrix[i][j] as int
    }
}


proof fn lemma_col_max_bounds(matrix: Seq<Vec<i32>>, j: int, k: int)
    requires
        0 <= k <= matrix.len(),
        0 <= j,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() > j,
        forall |i: int| 0 <= i < matrix.len() ==> -1 <= #[trigger] matrix[i][j] <= 100,
    ensures
        -1 <= spec_col_max(matrix, j, k) <= 100,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_col_max_bounds(matrix, j, k - 1);
    }
}


proof fn lemma_col_max_ge(matrix: Seq<Vec<i32>>, j: int, k: int)
    requires
        0 <= k <= matrix.len(),
        0 <= j,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() > j,
        forall |i: int| 0 <= i < matrix.len() ==> -1 <= #[trigger] matrix[i][j] <= 100,
    ensures
        forall |i: int| 0 <= i < k ==> spec_col_max(matrix, j, k) >= (#[trigger] matrix[i][j] as int),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_col_max_ge(matrix, j, k - 1);
    }
}


pub open spec fn col_has_nonneg(matrix: Seq<Vec<i32>>, j: int, k: int) -> bool
    decreases k,
{
    if k <= 0 {
        false
    } else if matrix[k - 1][j] >= 0 {
        true
    } else {
        col_has_nonneg(matrix, j, k - 1)
    }
}


proof fn lemma_col_max_nonneg(matrix: Seq<Vec<i32>>, j: int, k: int)
    requires
        0 <= k <= matrix.len(),
        0 <= j,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() > j,
        forall |i: int| 0 <= i < matrix.len() ==> -1 <= #[trigger] matrix[i][j] <= 100,
        col_has_nonneg(matrix, j, k),
    ensures
        spec_col_max(matrix, j, k) >= 0,
    decreases k,
{
    if k <= 0 {
    } else if matrix[k - 1][j] >= 0 {
        lemma_col_max_bounds(matrix, j, k);
        
    } else {
        lemma_col_max_nonneg(matrix, j, k - 1);
        
    }
}

impl Solution {
    pub fn modified_matrix(matrix: Vec<Vec<i32>>) -> (answer: Vec<Vec<i32>>)
        requires
            2 <= matrix.len() <= 50,
            2 <= matrix[0].len() <= 50,
            forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
            forall |i: int, j: int|
                0 <= i < matrix.len() && 0 <= j < matrix[i].len()
                ==> -1 <= #[trigger] matrix[i][j] <= 100,
            
            forall |j: int| 0 <= j < matrix[0].len()
                ==> #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int),
        ensures
            answer.len() == matrix.len(),
            forall |i: int| 0 <= i < answer.len()
                ==> #[trigger] answer[i].len() == matrix[0].len(),
            forall |i: int, j: int|
                0 <= i < answer.len() && 0 <= j < answer[i].len()
                ==> #[trigger] answer[i][j] as int == spec_answer_element(matrix@, i, j),
    {
        let m = matrix.len();
        let n = matrix[0].len();

        
        let mut col_max: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                m == matrix.len(),
                n == matrix[0].len(),
                2 <= m <= 50,
                2 <= n <= 50,
                forall |ii: int| 0 <= ii < m ==> #[trigger] matrix[ii].len() == n,
                forall |ii: int, jj: int|
                    0 <= ii < m && 0 <= jj < matrix[ii].len()
                    ==> -1 <= #[trigger] matrix[ii][jj] <= 100,
                forall |jj: int| 0 <= jj < n
                    ==> #[trigger] col_has_nonneg(matrix@, jj, m as int),
                0 <= j <= n,
                col_max.len() == j,
                forall |jj: int| 0 <= jj < j
                    ==> #[trigger] col_max[jj] as int == spec_col_max(matrix@, jj, m as int),
                forall |jj: int| 0 <= jj < j ==> -1 <= #[trigger] col_max[jj] <= 100,
                forall |jj: int| 0 <= jj < j ==> #[trigger] col_max[jj] >= 0,
            decreases n - j,
        {
            let mut mx: i32 = -1;
            let mut i: usize = 0;
            assert(matrix[i as int].len() == n);
            while i < m
                invariant
                    m == matrix.len(),
                    n == matrix[0].len(),
                    2 <= m <= 50,
                    2 <= n <= 50,
                    forall |ii: int| 0 <= ii < m ==> #[trigger] matrix[ii].len() == n,
                    forall |ii: int, jj: int|
                        0 <= ii < m && 0 <= jj < matrix[ii].len()
                        ==> -1 <= #[trigger] matrix[ii][jj] <= 100,
                    0 <= j < n,
                    0 <= i <= m,
                    mx as int == spec_col_max(matrix@, j as int, i as int),
                    -1 <= mx <= 100,
                decreases m - i,
            {
                assert(matrix[i as int].len() == n);
                if matrix[i][j] > mx {
                    mx = matrix[i][j];
                }
                i = i + 1;
            }
            proof {
                lemma_col_max_nonneg(matrix@, j as int, m as int);
            }
            assert(mx >= 0);
            col_max.push(mx);
            j = j + 1;
        }

        
        let mut answer: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                m == matrix.len(),
                n == matrix[0].len(),
                2 <= m <= 50,
                2 <= n <= 50,
                forall |ii: int| 0 <= ii < m ==> #[trigger] matrix[ii].len() == n,
                forall |ii: int, jj: int|
                    0 <= ii < m && 0 <= jj < matrix[ii].len()
                    ==> -1 <= #[trigger] matrix[ii][jj] <= 100,
                col_max.len() == n,
                forall |jj: int| 0 <= jj < n
                    ==> #[trigger] col_max[jj] as int == spec_col_max(matrix@, jj, m as int),
                forall |jj: int| 0 <= jj < n ==> #[trigger] col_max[jj] >= 0,
                0 <= i <= m,
                answer.len() == i,
                forall |ii: int| 0 <= ii < i
                    ==> #[trigger] answer[ii].len() == n,
                forall |ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < answer[ii].len()
                    ==> #[trigger] answer[ii][jj] as int == spec_answer_element(matrix@, ii, jj),
                forall |ii: int, jj: int|
                    0 <= ii < i && 0 <= jj < answer[ii].len()
                    ==> #[trigger] answer[ii][jj] >= 0,
            decreases m - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    m == matrix.len(),
                    n == matrix[0].len(),
                    2 <= m <= 50,
                    2 <= n <= 50,
                    forall |ii: int| 0 <= ii < m ==> #[trigger] matrix[ii].len() == n,
                    forall |ii: int, jj: int|
                        0 <= ii < m && 0 <= jj < matrix[ii].len()
                        ==> -1 <= #[trigger] matrix[ii][jj] <= 100,
                    col_max.len() == n,
                    forall |jj: int| 0 <= jj < n
                        ==> #[trigger] col_max[jj] as int == spec_col_max(matrix@, jj, m as int),
                    forall |jj: int| 0 <= jj < n ==> #[trigger] col_max[jj] >= 0,
                    0 <= i < m,
                    0 <= j <= n,
                    row.len() == j,
                    forall |jj: int| 0 <= jj < j
                        ==> #[trigger] row[jj] as int == spec_answer_element(matrix@, i as int, jj),
                    forall |jj: int| 0 <= jj < j
                        ==> #[trigger] row[jj] >= 0,
                decreases n - j,
            {
                assert(matrix[i as int].len() == n);
                if matrix[i][j] == -1 {
                    row.push(col_max[j]);
                } else {
                    row.push(matrix[i][j]);
                    assert(matrix[i as int][j as int] >= 0) by {
                        
                    }
                }
                j = j + 1;
            }
            answer.push(row);
            i = i + 1;
        }
        answer
    }
}

} 
