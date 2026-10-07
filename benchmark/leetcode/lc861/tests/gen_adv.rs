use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: usize, n: usize, bits: &Vec<i32>) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= m <= 20,
        1 <= n <= 20,
        bits.len() == m * n,
        forall|i: int| 0 <= i < bits.len() ==> 0 <= #[trigger] bits[i] <= 1,
    ensures
        true,
{
    let mut row: Vec<i32> = Vec::new();
    row.push(0);
    let mut grid: Vec<Vec<i32>> = Vec::new();
    grid.push(row);
    grid
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

fn print_json(grid: &Vec<Vec<i32>>) {
    print!("{{\"grid\":[");
    for i in 0..grid.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", grid[i][j]);
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
    let total = 200usize;
    let bits = vec![0];
    for _ in 0..total {
        let _ = rng.next_u64();
        let grid = generate_test_case(1, 1, &bits);
        print_json(&grid);
    }
}
