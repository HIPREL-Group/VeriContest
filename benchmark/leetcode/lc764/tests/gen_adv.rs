use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    mines_x: &Vec<i32>,
    mines_y: &Vec<i32>,
    row: usize,
    col: usize,
    value: i32,
) -> (result: (Vec<Vec<i32>>, usize, usize, i32))
    requires
        1 <= n <= 500,
        1 <= mines_x.len() <= 5000,
        mines_x.len() == mines_y.len(),
        forall|i: int| 0 <= i < mines_x.len() ==> 0 <= #[trigger] mines_x[i] < n,
        forall|i: int| 0 <= i < mines_y.len() ==> 0 <= #[trigger] mines_y[i] < n,
        forall|i: int, j: int| 0 <= i < j < mines_x.len() ==>
            (#[trigger] mines_x[i] != #[trigger] mines_x[j] || #[trigger] mines_y[i] != #[trigger] mines_y[j]),
        row < n as usize,
        col < n as usize,
    ensures
        true,
{
    let mut rowv: Vec<i32> = Vec::new();
    rowv.push(1);
    let mut grid: Vec<Vec<i32>> = Vec::new();
    grid.push(rowv);
    (grid, 0usize, 0usize, value)
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

fn print_json(n: i32, mines: &[(i32, i32)]) {
    print!("{{\"n\":{},\"mines\":[", n);
    for i in 0..mines.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", mines[i].0, mines[i].1);
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
    let mines_x = vec![0];
    let mines_y = vec![0];
    for t in 0..total {
        let value = (rng.next_u64() % 2) as i32;
        let (grid, row, col, v) = generate_test_case(1, &mines_x, &mines_y, 0, 0, value);
        let _ = (grid, row, col, v);
        let n = 1 + (t % 50) as i32;
        let mines: Vec<(i32, i32)> = if t % 3 == 0 {
            vec![]
        } else {
            vec![(0, 0)]
        };
        print_json(n, &mines);
    }
}
