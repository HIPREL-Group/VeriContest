use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    start: i32,
    target: i32,
) -> (matrix: Vec<Vec<i32>>)
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        -10_000 <= start <= 10_000,
        -10_000 <= target <= 10_000,
        // Ensure values are bounded: start + m*n - 1 <= 10_000
        start as int + (m as int) * (n as int) - 1 <= 10_000,
        start as int >= -10_000,
    ensures
        1 <= matrix.len() <= 100,
        1 <= matrix[0].len() <= 100,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
        forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len()
            ==> -10_000 <= #[trigger] matrix[i][j] <= 10_000,
        forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1 ==>
            #[trigger] matrix[i][j] <= matrix[i][j + 1],
        forall |i: int| 1 <= i < matrix.len() ==>
            #[trigger] matrix[i][0] > matrix[i - 1][matrix[0].len() - 1],
        -10_000 <= target <= 10_000,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            0 <= i <= m,
            1 <= m <= 100,
            1 <= n <= 100,
            matrix.len() == i,
            -10_000 <= start <= 10_000,
            start as int + (m as int) * (n as int) - 1 <= 10_000,
            start as int >= -10_000,
            forall |ii: int| 0 <= ii < i as int ==> #[trigger] matrix[ii].len() == n as int,
            forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < n as int ==>
                #[trigger] matrix[ii][jj] == start as int + ii * (n as int) + jj,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;

        // Prove: start + i*n is in i32 range
        proof {
            // i < m, n <= 100
            // start + i*n <= start + (m-1)*n <= start + m*n - 1 <= 10_000
            assert((i as int) * (n as int) <= (m as int - 1) * (n as int)) by (nonlinear_arith)
                requires i as int <= m as int - 1, n as int >= 0;
            assert((m as int - 1) * (n as int) == (m as int) * (n as int) - (n as int)) by (nonlinear_arith);
            assert((i as int) * (n as int) <= (m as int) * (n as int) - (n as int));
            assert((n as int) >= 1);
            assert((i as int) * (n as int) <= (m as int) * (n as int) - 1);
        }

        let row_base: i32 = start + (i as i32) * (n as i32);

        while j < n
            invariant
                0 <= j <= n,
                1 <= m <= 100,
                1 <= n <= 100,
                i < m,
                row.len() == j,
                -10_000 <= start <= 10_000,
                start as int + (m as int) * (n as int) - 1 <= 10_000,
                start as int >= -10_000,
                row_base as int == start as int + (i as int) * (n as int),
                forall |jj: int| 0 <= jj < j as int ==>
                    #[trigger] row[jj] == start as int + (i as int) * (n as int) + jj,
            decreases n - j,
        {
            proof {
                // row_base + j <= start + i*n + (n-1) <= start + (m-1)*n + (n-1) = start + m*n - 1 <= 10_000
                assert((i as int) * (n as int) + (j as int) <= (m as int - 1) * (n as int) + (n as int - 1)) by (nonlinear_arith)
                    requires i as int <= m as int - 1, j as int <= n as int - 1, n as int >= 1;
                assert((m as int - 1) * (n as int) + (n as int - 1) == (m as int) * (n as int) - 1) by (nonlinear_arith);
                assert((i as int) * (n as int) + (j as int) <= (m as int) * (n as int) - 1);
                assert(start as int + (i as int) * (n as int) + (j as int) <= 10_000);
                assert((i as int) * (n as int) >= 0) by (nonlinear_arith)
                    requires i as int >= 0, n as int >= 0;
                assert(start as int + (i as int) * (n as int) + (j as int) >= -10_000);
            }

            let v: i32 = row_base + (j as i32);
            row.push(v);
            j = j + 1;
        }

        matrix.push(row);
        i = i + 1;
    }

    proof {
        assert(matrix.len() == m as int);
        assert(matrix[0].len() == n as int);

        assert forall |ii: int, jj: int|
            0 <= ii < matrix.len() && 0 <= jj < matrix[ii].len()
            implies -10_000 <= #[trigger] matrix[ii][jj] <= 10_000
        by {
            assert(matrix[ii].len() == n as int);
            assert(matrix[ii][jj] == start as int + ii * (n as int) + jj);
            assert(ii * (n as int) >= 0) by (nonlinear_arith)
                requires ii >= 0, n as int >= 0;
            assert(ii * (n as int) + jj >= 0);
            assert(ii <= m as int - 1);
            assert(jj <= n as int - 1);
            assert(ii * (n as int) + jj <= (m as int - 1) * (n as int) + (n as int - 1)) by (nonlinear_arith)
                requires ii <= m as int - 1, jj <= n as int - 1, n as int >= 1;
            assert((m as int - 1) * (n as int) + (n as int - 1) == (m as int) * (n as int) - 1) by (nonlinear_arith);
        }

        assert forall |ii: int, jj: int|
            0 <= ii < matrix.len() && 0 <= jj < matrix[ii].len() - 1
            implies #[trigger] matrix[ii][jj] <= matrix[ii][jj + 1]
        by {
            assert(matrix[ii].len() == n as int);
            assert(matrix[ii][jj] == start as int + ii * (n as int) + jj);
            assert(matrix[ii][jj + 1] == start as int + ii * (n as int) + (jj + 1));
        }

        assert forall |ii: int|
            1 <= ii < matrix.len()
            implies #[trigger] matrix[ii][0] > matrix[ii - 1][matrix[0].len() - 1]
        by {
            assert(matrix[0].len() == n as int);
            assert(matrix[ii].len() == n as int);
            assert(matrix[ii - 1].len() == n as int);
            assert(matrix[ii][0] == start as int + ii * (n as int));
            assert(matrix[ii - 1][(n as int) - 1] == start as int + (ii - 1) * (n as int) + (n as int - 1));
            assert(ii * (n as int) == (ii - 1) * (n as int) + (n as int)) by (nonlinear_arith);
        }
    }

    matrix
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_dimensions(rng: &mut Rng, mode: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, rng.gen_range_usize(1, 100)),
        2 => (rng.gen_range_usize(1, 100), 1),
        3 => (100, 100),
        4 => (10, 10),
        5 => (rng.gen_range_usize(2, 20), rng.gen_range_usize(2, 20)),
        6 => (3, 4),
        7 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
        8 => (50, 2),
        9 => (2, 50),
        _ => (rng.gen_range_usize(1, 100), rng.gen_range_usize(1, 100)),
    }
}

fn pick_start_and_target(rng: &mut Rng, m: usize, n: usize, mode: usize) -> (i32, i32) {
    let total = (m * n) as i32;
    // start range such that start + m*n - 1 <= 10_000 and start >= -10_000
    let max_start = 10_000 - (total - 1);
    let min_start = -10_000;
    let start = rng.gen_range_i32(min_start, max_start);
    let end = start + total - 1;

    let target = match mode {
        0 => start,                                  // first element
        1 => end,                                    // last element
        2 => {
            if total > 1 {
                start + rng.gen_range_i32(0, total - 1)
            } else {
                start
            }
        }
        3 => {
            // not present - below
            if start > -10_000 { start - 1 } else { end + 1 }
        }
        4 => {
            // not present - above
            if end < 10_000 { end + 1 } else { start - 1 }
        }
        5 => {
            // middle
            start + total / 2
        }
        6 => {
            // random value in the target range
            rng.gen_range_i32(-10_000, 10_000)
        }
        7 => {
            // end of first row style - just boundary element
            if n > 0 && m > 0 {
                start + (n as i32) - 1
            } else {
                start
            }
        }
        8 => {
            // first element of second row
            if m >= 2 {
                start + (n as i32)
            } else {
                start
            }
        }
        9 => -10_000,
        _ => 10_000,
    };

    let target = if target < -10_000 { -10_000 } else if target > 10_000 { 10_000 } else { target };
    (start, target)
}

fn print_json(matrix: &Vec<Vec<i32>>, target: i32) {
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
    println!("],\"target\":{}}}", target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n) = pick_dimensions(&mut rng, mode);
        // ensure bounds
        let m = if m < 1 { 1 } else if m > 100 { 100 } else { m };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };

        let (start, target) = pick_start_and_target(&mut rng, m, n, (t / modes) % modes);

        // Double-check bounds before calling
        let total_elem = (m as i32) * (n as i32);
        if start as i64 + total_elem as i64 - 1 > 10_000 { continue; }
        if (start as i64) < -10_000 { continue; }
        if target < -10_000 || target > 10_000 { continue; }

        let matrix = generate_test_case(m, n, start, target);
        print_json(&matrix, target);
    }
}