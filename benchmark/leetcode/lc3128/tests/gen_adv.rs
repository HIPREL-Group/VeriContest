use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    bits: &Vec<Vec<i32>>,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= rows <= 1000,
        1 <= cols <= 1000,
        bits.len() == rows,
        forall |r: int| 0 <= r < bits.len() ==> (#[trigger] bits[r]).len() == cols,
        forall |r: int, c: int| 0 <= r < bits.len() && 0 <= c < bits[r].len() ==> {
            let v = #[trigger] bits[r][c];
            v == 0 || v == 1
        },
    ensures
        1 <= grid.len() <= 1000,
        1 <= grid[0].len() <= 1000,
        forall |r: int| 0 <= r < grid.len() ==> (#[trigger] grid[r]).len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
            let v = #[trigger] grid[r][c];
            v == 0 || v == 1
        },
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            1 <= rows <= 1000,
            1 <= cols <= 1000,
            bits.len() == rows,
            0 <= i <= rows,
            grid.len() == i,
            forall |r: int| 0 <= r < bits.len() ==> (#[trigger] bits[r]).len() == cols,
            forall |r: int, c: int| 0 <= r < bits.len() && 0 <= c < bits[r].len() ==> {
                let v = #[trigger] bits[r][c];
                v == 0 || v == 1
            },
            forall |r: int| 0 <= r < grid.len() ==> (#[trigger] grid[r]).len() == cols,
            forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> {
                let v = #[trigger] grid[r][c];
                v == 0 || v == 1
            },
        decreases rows - i,
    {
        let src = &bits[i];
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j <= cols,
                row.len() == j,
                src.len() == cols,
                forall |c: int| 0 <= c < src.len() ==> {
                    let v = #[trigger] src[c];
                    v == 0 || v == 1
                },
                forall |c: int| 0 <= c < row.len() ==> {
                    let v = #[trigger] row[c];
                    v == 0 || v == 1
                },
            decreases cols - j,
        {
            let v = src[j];
            row.push(v);
            j = j + 1;
        }
        grid.push(row);
        i = i + 1;
    }
    grid
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self, prob_one_pct: u32) -> i32 {
        let v = (self.next_u64() % 100) as u32;
        if v < prob_one_pct { 1 } else { 0 }
    }
}

fn make_bits(rng: &mut Rng, rows: usize, cols: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut bits: Vec<Vec<i32>> = Vec::with_capacity(rows);
    for i in 0..rows {
        let mut row: Vec<i32> = Vec::with_capacity(cols);
        for j in 0..cols {
            let v: i32 = match mode {
                0 => 0,
                1 => 1,
                2 => rng.gen_bit(50),
                3 => rng.gen_bit(10),
                4 => rng.gen_bit(90),
                5 => if i == 0 || j == 0 { 1 } else { 0 },
                6 => if i == j { 1 } else { 0 },
                7 => if i == 0 || i + 1 == rows || j == 0 || j + 1 == cols { 1 } else { 0 },
                8 => if (i + j) % 2 == 0 { 1 } else { 0 },
                9 => rng.gen_bit(5),
                10 => rng.gen_bit(95),
                11 => if j == cols / 2 { 1 } else { 0 },
                12 => if i == rows / 2 { 1 } else { 0 },
                _ => rng.gen_bit(30),
            };
            row.push(v);
        }
        bits.push(row);
    }
    bits
}

fn print_json(grid: &Vec<Vec<i32>>) {
    print!("{{\"grid\":[");
    for i in 0..grid.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..grid[i].len() {
            if j > 0 { print!(","); }
            print!("{}", grid[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 13usize;

    for t in 0..total {
        let mode = t % modes;
        let (rows, cols) = match t % 10 {
            0 => (1usize, 1usize),
            1 => (1, rng.gen_range_usize(1, 50)),
            2 => (rng.gen_range_usize(1, 50), 1),
            3 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),
            4 => (rng.gen_range_usize(10, 30), rng.gen_range_usize(10, 30)),
            5 => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)),
            6 => (3, 3),
            7 => (rng.gen_range_usize(1, 20), rng.gen_range_usize(1, 20)),
            8 => (rng.gen_range_usize(20, 80), rng.gen_range_usize(20, 80)),
            _ => (rng.gen_range_usize(1, 40), rng.gen_range_usize(1, 40)),
        };

        let bits = make_bits(&mut rng, rows, cols, mode);
        let grid = generate_test_case(rows, cols, &bits);
        print_json(&grid);
    }
}