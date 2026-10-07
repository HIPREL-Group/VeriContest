use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    diag: &Vec<i32>,  // length m + n - 1, diag[k] is the value for cells with i - j + (n-1) == k
) -> (matrix: Vec<Vec<i32>>)
    requires
        1 <= m <= 20,
        1 <= n <= 20,
        diag.len() == m + n - 1,
        forall |k: int| 0 <= k < diag.len() ==> 0 <= #[trigger] diag[k] <= 99,
    ensures
        1 <= matrix.len() <= 20,
        forall |i: int| 0 <= i < matrix.len() ==> 1 <= #[trigger] matrix[i].len() <= 20,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
        forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[0].len() ==> 0 <= #[trigger] matrix[i][j] <= 99,
        matrix.len() == m,
        matrix[0].len() == n,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 20,
            1 <= n <= 20,
            diag.len() == m + n - 1,
            0 <= i <= m,
            matrix.len() == i,
            forall |ii: int| 0 <= ii < matrix.len() ==> (#[trigger] matrix[ii]).len() == n,
            forall |ii: int, jj: int| 0 <= ii < matrix.len() && 0 <= jj < n as int
                ==> 0 <= #[trigger] matrix[ii][jj] <= 99,
            forall |k: int| 0 <= k < diag.len() ==> 0 <= #[trigger] diag[k] <= 99,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 20,
                0 <= j <= n,
                row.len() == j,
                i < m,
                diag.len() == m + n - 1,
                forall |jj: int| 0 <= jj < row.len() ==> 0 <= #[trigger] row[jj] <= 99,
                forall |k: int| 0 <= k < diag.len() ==> 0 <= #[trigger] diag[k] <= 99,
            decreases n - j,
        {
            // index i - j + (n-1)
            let k: usize = i + (n - 1) - j;
            assert(k < m + n - 1);
            let v = diag[k];
            row.push(v);
            j = j + 1;
        }
        assert(row.len() == n);
        matrix.push(row);
        i = i + 1;
    }

    assert(matrix.len() == m);
    assert(matrix[0].len() == n);

    matrix
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u32;
        lo + (self.next_u64() as u32 % span) as i32
    }
}

fn build_matrix(m: usize, n: usize, diag: &Vec<i32>, breaks: &[(usize, usize, i32)]) -> Vec<Vec<i32>> {
    // First build Toeplitz matrix, then apply breaks (cells to overwrite)
    let mut mat = generate_test_case(m, n, diag);
    for &(i, j, v) in breaks {
        if i < m && j < n && v >= 0 && v <= 99 {
            mat[i][j] = v;
        }
    }
    mat
}

fn print_json(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for i in 0..matrix.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..matrix[i].len() {
            if j > 0 { print!(","); }
            print!("{}", matrix[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn random_diag(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut d = Vec::with_capacity(len);
    for _ in 0..len {
        d.push(rng.gen_range_i32(0, 99));
    }
    d
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let (m, n) = match mode {
            0 => (1usize, 1usize),
            1 => (1, rng.gen_range_usize(1, 20)),
            2 => (rng.gen_range_usize(1, 20), 1),
            3 => (20, 20),
            4 => (2, 2),
            5 => (rng.gen_range_usize(2, 20), rng.gen_range_usize(2, 20)),
            6 => (rng.gen_range_usize(1, 20), rng.gen_range_usize(1, 20)),
            7 => (20, rng.gen_range_usize(1, 20)),
            8 => (rng.gen_range_usize(1, 20), 20),
            _ => (rng.gen_range_usize(1, 20), rng.gen_range_usize(1, 20)),
        };

        let diag_len = m + n - 1;
        let diag = random_diag(&mut rng, diag_len);

        // Decide breaks - sometimes introduce non-Toeplitz violations
        let mut breaks: Vec<(usize, usize, i32)> = Vec::new();
        let break_mode = rng.next_u64() % 5;
        if break_mode == 0 && m >= 2 && n >= 2 {
            // single random break
            let bi = rng.gen_range_usize(1, m - 1);
            let bj = rng.gen_range_usize(1, n - 1);
            let bv = rng.gen_range_i32(0, 99);
            breaks.push((bi, bj, bv));
        } else if break_mode == 1 && m >= 2 && n >= 2 {
            // break at (0,0) equivalent - change top-left
            breaks.push((0, 0, rng.gen_range_i32(0, 99)));
        } else if break_mode == 2 && m >= 2 && n >= 2 {
            // break corner (m-1, n-1)
            breaks.push((m - 1, n - 1, rng.gen_range_i32(0, 99)));
        }

        let mat = build_matrix(m, n, &diag, &breaks);
        print_json(&mat);
    }
}