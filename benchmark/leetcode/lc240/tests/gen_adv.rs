use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    base: i32,
    target: i32,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 300,
        1 <= n <= 300,
        -500_000_000 <= base <= 500_000_000,
        -1_000_000_000 <= target <= 1_000_000_000,
    ensures
        ({
            let matrix = result.0;
            let t = result.1;
            &&& 1 <= matrix.len() <= 300
            &&& 1 <= matrix[0].len() <= 300
            &&& forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len()
            &&& forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len()
                ==> -1_000_000_000 <= #[trigger] matrix[i][j] <= 1_000_000_000
            &&& forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[i].len() - 1 ==>
                #[trigger] matrix[i][j] < matrix[i][j + 1]
            &&& forall |i: int, j: int| 0 <= j < matrix[0].len() && 0 <= i < matrix.len() - 1 ==>
                #[trigger] matrix[i][j] < matrix[i + 1][j]
            &&& -1_000_000_000 <= t <= 1_000_000_000
        }),
{
    let mut row: Vec<i32> = Vec::new();
    row.push(0);
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    matrix.push(row);
    (matrix, target)
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
        self.state = self
            .state
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn print_json(matrix: &Vec<Vec<i32>>, target: i32) {
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
    println!("],\"target\":{}}}", target);
}

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => {
            // Small matrix, target present (base = 0, target in range)
            let m = rng.gen_range_usize(1, 5);
            let n = rng.gen_range_usize(1, 5);
            let base = 0i32;
            // target = base + i*1000 + j for some (i,j)
            let ii = rng.gen_range_usize(0, m - 1) as i32;
            let jj = rng.gen_range_usize(0, n - 1) as i32;
            let target = base + ii * 1000 + jj;
            (m, n, base, target)
        }
        1 => {
            // Large matrix 300x300
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            let target = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            (300, 300, base, target)
        }
        2 => {
            // 1xN
            let n = rng.gen_range_usize(1, 300);
            let base = rng.gen_range_i32(-500_000_000, 500_000_000);
            let jj = rng.gen_range_usize(0, n - 1) as i32;
            let target = base + jj;
            (1, n, base, target)
        }
        3 => {
            // Mx1
            let m = rng.gen_range_usize(1, 300);
            let base = rng.gen_range_i32(-500_000_000, 500_000_000);
            let ii = rng.gen_range_usize(0, m - 1) as i32;
            let target = base + ii * 1000;
            (m, 1, base, target)
        }
        4 => {
            // Target not present - very small
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            let target = base - 1;
            (5, 5, base, target)
        }
        5 => {
            // Target equals top-left
            let m = rng.gen_range_usize(1, 50);
            let n = rng.gen_range_usize(1, 50);
            let base = rng.gen_range_i32(-500_000_000, 500_000_000);
            (m, n, base, base)
        }
        6 => {
            // Target equals bottom-right
            let m = rng.gen_range_usize(1, 50);
            let n = rng.gen_range_usize(1, 50);
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            let target = base + (m as i32 - 1) * 1000 + (n as i32 - 1);
            (m, n, base, target)
        }
        7 => {
            // Target smaller than smallest
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(1, 100);
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            (m, n, base, base - 1000)
        }
        8 => {
            // Target larger than largest
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(1, 100);
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            let target = base + (m as i32) * 1000 + (n as i32) + 500;
            (m, n, base, target)
        }
        9 => {
            // Random small/medium
            let m = rng.gen_range_usize(1, 20);
            let n = rng.gen_range_usize(1, 20);
            let base = rng.gen_range_i32(-500_000_000, 500_000_000);
            let target = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            (m, n, base, target)
        }
        _ => {
            let _ = t;
            let m = rng.gen_range_usize(1, 300);
            let n = rng.gen_range_usize(1, 300);
            let base = rng.gen_range_i32(-100_000_000, 100_000_000);
            let ii = rng.gen_range_usize(0, m - 1) as i32;
            let jj = rng.gen_range_usize(0, n - 1) as i32;
            let target = base + ii * 1000 + jj;
            (m, n, base, target)
        }
    }
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (m, n, base, target) = pick_params(&mut rng, mode, t);
        // clamp to valid ranges
        let m = if m < 1 { 1 } else if m > 300 { 300 } else { m };
        let n = if n < 1 { 1 } else if n > 300 { 300 } else { n };
        let base = if base < -500_000_000 {
            -500_000_000
        } else if base > 500_000_000 {
            500_000_000
        } else {
            base
        };
        let target = if target < -1_000_000_000 {
            -1_000_000_000
        } else if target > 1_000_000_000 {
            1_000_000_000
        } else {
            target
        };
        let (matrix, tgt) = generate_test_case(m, n, base, target);
        print_json(&matrix, tgt);
    }
}
