use vstd::prelude::*;

verus! {

/// Maximum element in column j of matrix, considering rows [0..k)
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

/// True when column j has at least one non-negative element in rows [0..k)
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

proof fn lemma_col_has_nonneg_extend(matrix: Seq<Vec<i32>>, j: int, k: int)
    requires
        0 < k <= matrix.len(),
        matrix[k - 1][j] >= 0,
    ensures
        col_has_nonneg(matrix, j, k),
    decreases k,
{
}

pub fn generate_test_case(
    m: usize,
    n: usize,
    vals: &Vec<Vec<i32>>,
) -> (matrix: Vec<Vec<i32>>)
    requires
        2 <= m <= 50,
        2 <= n <= 50,
        vals.len() == m,
        forall |i: int| 0 <= i < m as int ==> #[trigger] vals[i].len() == n as int,
        forall |i: int, j: int|
            0 <= i < m as int && 0 <= j < n as int
            ==> 0 <= #[trigger] vals[i][j] <= 100,
    ensures
        2 <= matrix.len() <= 50,
        matrix.len() == m,
        2 <= matrix[0].len() <= 50,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == n as int,
        forall |i: int, j: int|
            0 <= i < matrix.len() && 0 <= j < matrix[i].len()
            ==> -1 <= #[trigger] matrix[i][j] <= 100,
        forall |j: int| 0 <= j < matrix[0].len()
            ==> #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int),
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            2 <= m <= 50,
            2 <= n <= 50,
            vals.len() == m,
            0 <= i <= m,
            matrix.len() == i,
            forall |ii: int| 0 <= ii < m as int ==> #[trigger] vals[ii].len() == n as int,
            forall |ii: int, jj: int|
                0 <= ii < m as int && 0 <= jj < n as int
                ==> 0 <= #[trigger] vals[ii][jj] <= 100,
            forall |ii: int| 0 <= ii < i as int ==> #[trigger] matrix[ii].len() == n as int,
            forall |ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < n as int
                ==> 0 <= #[trigger] matrix[ii][jj] <= 100,
            forall |ii: int, jj: int|
                0 <= ii < i as int && 0 <= jj < n as int
                ==> #[trigger] matrix[ii][jj] == vals[ii][jj],
        decreases m - i,
    {
        let row = vals[i].clone();
        assert(row.len() == n as int);
        matrix.push(row);
        i = i + 1;
    }

    proof {
        assert(matrix.len() == m);
        assert(matrix[0].len() == n as int);

        assert forall |ii: int, jj: int|
            0 <= ii < matrix.len() && 0 <= jj < matrix[ii].len()
            implies -1 <= #[trigger] matrix[ii][jj] <= 100
        by {
            assert(matrix[ii].len() == n as int);
            assert(0 <= matrix[ii][jj] <= 100);
        }

        assert forall |j: int| 0 <= j < matrix[0].len()
            implies #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int)
        by {
            assert(matrix.len() == m);
            assert(m >= 2);
            // row 0 has nonneg value at column j since vals[0][j] >= 0
            assert(matrix[0].len() == n as int);
            assert(matrix[0][j] == vals[0int][j]);
            assert(vals[0int][j] >= 0);
            assert(matrix[0][j] >= 0);
            // Need: col_has_nonneg(matrix@, j, m as int) when matrix@[0][j] >= 0
            // Prove by induction going up from k=1
            lemma_col_has_nonneg_from_first(matrix@, j, matrix.len() as int);
        }
    }

    matrix
}

proof fn lemma_col_has_nonneg_from_first(matrix: Seq<Vec<i32>>, j: int, k: int)
    requires
        1 <= k <= matrix.len(),
        matrix[0].len() > j,
        j >= 0,
        matrix[0][j] >= 0,
    ensures
        col_has_nonneg(matrix, j, k),
    decreases k,
{
    if k == 1 {
        assert(matrix[k - 1][j] >= 0);
    } else {
        lemma_col_has_nonneg_from_first(matrix, j, k - 1);
    }
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, m: usize, n: usize, mode: usize) -> Vec<Vec<i32>> {
    // Always make vals nonneg (0..=100); the spec ensures col_has_nonneg trivially because row 0 is nonneg.
    // The "-1" element semantics in the actual problem live inside the spec's interpretation,
    // but we must produce matrix elements in [0..=100] satisfying the generator's precondition.
    // (We pass nonneg values; that's a valid subset of the original problem's input space.)
    let mut rows: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let v = match mode {
                0 => rng.gen_range_i32(0, 100),
                1 => {
                    if (i + j) % 2 == 0 { 0 } else { 100 }
                }
                2 => 0,
                3 => 100,
                4 => {
                    if i == 0 { rng.gen_range_i32(0, 100) }
                    else { rng.gen_range_i32(0, 100) }
                }
                5 => {
                    // Monotone increasing per column
                    ((i as i32 * 3 + j as i32) % 101).max(0)
                }
                6 => {
                    // Max at row 0
                    if i == 0 { 100 } else { rng.gen_range_i32(0, 50) }
                }
                7 => {
                    // Max at last row
                    if i + 1 == m { 100 } else { rng.gen_range_i32(0, 50) }
                }
                8 => {
                    // All same
                    42
                }
                9 => {
                    // Distinct-ish
                    ((i as i32 * 7 + j as i32 * 13) % 101).abs()
                }
                _ => rng.gen_range_i32(0, 100),
            };
            let vv = if v < 0 { 0 } else if v > 100 { 100 } else { v };
            row.push(vv);
        }
        rows.push(row);
    }
    rows
}

fn print_json(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for i in 0..matrix.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..matrix[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", matrix[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let m = match mode {
            0 => 2 + (t % 10),
            1 => 50,
            2 => 2,
            3 => 50,
            4 => 10 + (t % 20),
            5 => 25,
            6 => 5 + (t % 15),
            7 => 5 + (t % 15),
            8 => 2 + (t % 49),
            _ => 3 + (t % 30),
        };
        let n = match mode {
            0 => 2 + ((t / 2) % 10),
            1 => 50,
            2 => 50,
            3 => 2,
            4 => 5 + (t % 25),
            5 => 25,
            6 => 5 + (t % 15),
            7 => 5 + (t % 15),
            8 => 2 + ((t + 3) % 49),
            _ => 3 + ((t + 1) % 30),
        };
        let m = if m < 2 { 2 } else if m > 50 { 50 } else { m };
        let n = if n < 2 { 2 } else if n > 50 { 50 } else { n };

        let vals = build_vals(&mut rng, m, n, mode);
        let matrix = generate_test_case(m, n, &vals);
        print_json(&matrix);
    }
}