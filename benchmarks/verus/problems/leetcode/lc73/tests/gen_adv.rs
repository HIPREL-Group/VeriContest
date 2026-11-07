use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    flat: &Vec<i32>,
    row: usize,
    col: usize,
    value: i32,
) -> (result: (Vec<Vec<i32>>, usize, usize, i32))
    requires
        1 <= m <= 200,
        1 <= n <= 200,
        flat.len() == m * n,
        row < m,
        col < n,
    ensures
        true,
{
    let mut rowv: Vec<i32> = Vec::new();
    rowv.push(0);
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    matrix.push(rowv);
    (matrix, 0usize, 0usize, value)
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
}

fn print_json(matrix: &Vec<Vec<i32>>, row: usize, col: usize, value: i32) {
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
    println!("],\"row\":{},\"col\":{},\"value\":{}}}", row, col, value);
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
    let flat = vec![0];
    for _ in 0..total {
        let value = (rng.next_u64() % 2001) as i32 - 1000;
        let (matrix, row, col, v) = generate_test_case(1, 1, &flat, 0, 0, value);
        print_json(&matrix, row, col, v);
    }
}
