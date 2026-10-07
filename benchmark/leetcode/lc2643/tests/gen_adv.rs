use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    bits: &Vec<Vec<i32>>,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 100,
        1 <= n <= 100,
        bits.len() == m,
        forall|i: int| 0 <= i < m as int ==> (#[trigger] bits[i]).len() == n,
        forall|i: int, j: int| 0 <= i < m as int && 0 <= j < n as int ==>
            (#[trigger] bits[i][j]) == 0 || bits[i][j] == 1,
    ensures
        mat.len() > 0,
        mat.len() <= 2147483647usize,
        mat.len() == m,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            1 <= m <= 100,
            1 <= n <= 100,
            bits.len() == m,
            forall|ii: int| 0 <= ii < m as int ==> (#[trigger] bits[ii]).len() == n,
            forall|ii: int, jj: int| 0 <= ii < m as int && 0 <= jj < n as int ==>
                (#[trigger] bits[ii][jj]) == 0 || bits[ii][jj] == 1,
            0 <= i <= m,
            mat.len() == i,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 100,
                0 <= j <= n,
                row.len() == j,
                i < m,
                bits.len() == m,
                bits[i as int].len() == n,
                forall|jj: int| 0 <= jj < n as int ==>
                    (#[trigger] bits[i as int][jj]) == 0 || bits[i as int][jj] == 1,
            decreases n - j,
        {
            row.push(bits[i][j]);
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }
    mat
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
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn build_bits(m: usize, n: usize, mode: usize, rng: &mut Rng) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::with_capacity(m);
    for i in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let b: i32 = match mode {
                0 => rng.gen_bit(),
                1 => 0,
                2 => 1,
                3 => if i == 0 { 1 } else { 0 },
                4 => if i == m - 1 { 1 } else { 0 },
                5 => if i == m / 2 { 1 } else { 0 },
                6 => {
                    // row i has exactly i ones
                    if j < i { 1 } else { 0 }
                }
                7 => {
                    // row i has m - i ones
                    if j < (m - i) % (n + 1) { 1 } else { 0 }
                }
                8 => {
                    // checkerboard
                    if (i + j) % 2 == 0 { 1 } else { 0 }
                }
                9 => {
                    // all rows have same count of ones -> tie, earliest row wins
                    if j % 2 == 0 { 1 } else { 0 }
                }
                _ => rng.gen_bit(),
            };
            row.push(b);
        }
        bits.push(row);
    }
    bits
}

fn print_json(mat: &Vec<Vec<i32>>) {
    print!("{{\"mat\":[");
    for i in 0..mat.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..mat[i].len() {
            if j > 0 { print!(","); }
            print!("{}", mat[i][j]);
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
            0 => rng.gen_range_usize(1, 20),
            1 => 1,
            2 => 100,
            3 => rng.gen_range_usize(1, 100),
            4 => rng.gen_range_usize(2, 50),
            5 => rng.gen_range_usize(3, 50),
            6 => rng.gen_range_usize(1, 20),
            7 => rng.gen_range_usize(1, 20),
            8 => rng.gen_range_usize(2, 50),
            9 => rng.gen_range_usize(1, 30),
            _ => rng.gen_range_usize(1, 100),
        };
        let n = match mode {
            0 => rng.gen_range_usize(1, 20),
            1 => rng.gen_range_usize(1, 100),
            2 => rng.gen_range_usize(1, 100),
            3 => rng.gen_range_usize(1, 100),
            4 => rng.gen_range_usize(2, 50),
            5 => rng.gen_range_usize(3, 50),
            6 => rng.gen_range_usize(1, 20),
            7 => rng.gen_range_usize(1, 20),
            8 => rng.gen_range_usize(2, 50),
            9 => rng.gen_range_usize(2, 30),
            _ => rng.gen_range_usize(1, 100),
        };
        let bits = build_bits(m, n, mode, &mut rng);
        let mat = generate_test_case(m, n, &bits);
        print_json(&mat);
    }
}