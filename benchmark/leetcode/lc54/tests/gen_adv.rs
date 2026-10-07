use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: usize, n: usize, val: i32) -> (matrix: Vec<Vec<i32>>)
    requires
        1 <= m <= 10,
        1 <= n <= 10,
        -100 <= val <= 100,
    ensures
        1 <= matrix.len() <= 10,
        matrix.len() == m,
        1 <= matrix[0].len() <= 10,
        matrix[0].len() == n,
        forall |r: int| 0 <= r < matrix.len() ==> (#[trigger] matrix[r]).len() == matrix[0].len(),
        forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -100 <= #[trigger] matrix[r][c] <= 100,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 10,
            1 <= n <= 10,
            -100 <= val <= 100,
            0 <= i <= m,
            matrix.len() == i,
            forall |r: int| 0 <= r < matrix.len() ==> (#[trigger] matrix[r]).len() == n,
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -100 <= #[trigger] matrix[r][c] <= 100,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 10,
                -100 <= val <= 100,
                0 <= j <= n,
                row.len() == j,
                forall |c: int| 0 <= c < row.len() ==> -100 <= #[trigger] row[c] <= 100,
            decreases n - j,
        {
            row.push(val);
            j = j + 1;
        }
        assert(row.len() == n);
        matrix.push(row);
        i = i + 1;
    }
    assert(matrix.len() == m);
    matrix
}

}

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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn print_matrix(matrix: &Vec<Vec<i32>>) {
    print!("{{\"matrix\":[");
    for r in 0..matrix.len() {
        if r > 0 { print!(","); }
        print!("[");
        for c in 0..matrix[r].len() {
            if c > 0 { print!(","); }
            print!("{}", matrix[r][c]);
        }
        print!("]");
    }
    println!("]}}");
}

fn build_matrix(m: usize, n: usize, vals: &[Vec<i32>]) -> Vec<Vec<i32>> {
    // fallback: use generate_test_case for uniform, but we want varied values
    // So build manually and then print directly (we won't re-verify)
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    for i in 0..m {
        let mut row: Vec<i32> = Vec::new();
        for j in 0..n {
            row.push(vals[i][j]);
        }
        matrix.push(row);
    }
    matrix
}

fn print_custom(m: usize, n: usize, vals: &Vec<Vec<i32>>) {
    let matrix = build_matrix(m, n, vals);
    print_matrix(&matrix);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    // Adversarial dimensions
    let dims: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (1, 10), (10, 1),
        (2, 2), (3, 3), (10, 10), (2, 10), (10, 2),
        (3, 4), (4, 3), (5, 5), (1, 5), (5, 1),
        (2, 3), (3, 2), (4, 5), (5, 4), (6, 7),
    ];

    // First, use verified generator for simple uniform cases
    let vals_uniform: Vec<i32> = vec![0, 1, -1, 100, -100, 42, -50];
    let mut count = 0;
    for &(m, n) in &dims {
        for &v in &vals_uniform {
            let matrix = generate_test_case(m, n, v);
            print_matrix(&matrix);
            count += 1;
            if count >= 70 { break; }
        }
        if count >= 70 { break; }
    }

    // Then, generate varied matrices using verified generator then overwriting values
    // But to keep things simple and still valid, re-use verified with random single val
    for _ in 0..60 {
        let m = rng.gen_range_usize(1, 10);
        let n = rng.gen_range_usize(1, 10);
        let v = rng.gen_range_i32(-100, 100);
        let matrix = generate_test_case(m, n, v);
        print_matrix(&matrix);
    }

    // Build varied matrices manually (values still within -100..=100, dims 1..=10)
    // These are valid inputs per spec; we print them directly.
    for _ in 0..70 {
        let m = rng.gen_range_usize(1, 10);
        let n = rng.gen_range_usize(1, 10);
        let mut vals: Vec<Vec<i32>> = Vec::new();
        for _ in 0..m {
            let mut row: Vec<i32> = Vec::new();
            for _ in 0..n {
                row.push(rng.gen_range_i32(-100, 100));
            }
            vals.push(row);
        }
        print_custom(m, n, &vals);
    }

    // Adversarial: boundary values
    for _ in 0..20 {
        let m = rng.gen_range_usize(1, 10);
        let n = rng.gen_range_usize(1, 10);
        let mut vals: Vec<Vec<i32>> = Vec::new();
        for i in 0..m {
            let mut row: Vec<i32> = Vec::new();
            for j in 0..n {
                let v = if (i + j) % 2 == 0 { 100 } else { -100 };
                row.push(v);
            }
            vals.push(row);
        }
        print_custom(m, n, &vals);
    }

    // Sequential values 1..=m*n (classic spiral test)
    for &(m, n) in &dims {
        let mut vals: Vec<Vec<i32>> = Vec::new();
        let mut k: i32 = 1;
        for _ in 0..m {
            let mut row: Vec<i32> = Vec::new();
            for _ in 0..n {
                let v = if k > 100 { k - 200 } else { k };
                row.push(v.max(-100).min(100));
                k += 1;
            }
            vals.push(row);
        }
        print_custom(m, n, &vals);
    }
}
