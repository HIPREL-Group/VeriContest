use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    start_row: usize,
    start_col: usize,
    home_row: usize,
    home_col: usize,
    row_costs: Vec<i32>,
    col_costs: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>))
    requires
        1 <= m <= 100_000,
        1 <= n <= 100_000,
        row_costs.len() == m,
        col_costs.len() == n,
        start_row < m,
        home_row < m,
        start_col < n,
        home_col < n,
        start_row <= 2_000_000_000,
        start_col <= 2_000_000_000,
        home_row <= 2_000_000_000,
        home_col <= 2_000_000_000,
        forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
        forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
    ensures
        result.0.len() == 2,
        result.1.len() == 2,
        1 <= result.2.len() <= 100_000,
        1 <= result.3.len() <= 100_000,
        forall |i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] <= 10_000,
        forall |i: int| 0 <= i < result.3.len() ==> 0 <= #[trigger] result.3[i] <= 10_000,
        0 <= result.0[0] < result.2.len(),
        0 <= result.1[0] < result.2.len(),
        0 <= result.0[1] < result.3.len(),
        0 <= result.1[1] < result.3.len(),
{
    let mut start_pos: Vec<i32> = Vec::new();
    start_pos.push(start_row as i32);
    start_pos.push(start_col as i32);

    let mut home_pos: Vec<i32> = Vec::new();
    home_pos.push(home_row as i32);
    home_pos.push(home_col as i32);

    assert(start_pos.len() == 2);
    assert(home_pos.len() == 2);
    assert(start_pos[0] == start_row as i32);
    assert(start_pos[1] == start_col as i32);
    assert(home_pos[0] == home_row as i32);
    assert(home_pos[1] == home_col as i32);

    (start_pos, home_pos, row_costs, col_costs)
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

fn make_costs(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    for _ in 0..len {
        let c = match mode {
            0 => 0,
            1 => 10_000,
            2 => rng.gen_range_i32(0, 1),
            3 => rng.gen_range_i32(9_999, 10_000),
            _ => rng.gen_range_i32(0, 10_000),
        };
        v.push(c);
    }
    v
}

fn print_json(sp: &Vec<i32>, hp: &Vec<i32>, rc: &Vec<i32>, cc: &Vec<i32>) {
    print!("{{\"start_pos\":[{},{}],\"home_pos\":[{},{}],\"row_costs\":[", sp[0], sp[1], hp[0], hp[1]);
    for i in 0..rc.len() {
        if i > 0 { print!(","); }
        print!("{}", rc[i]);
    }
    print!("],\"col_costs\":[");
    for i in 0..cc.len() {
        if i > 0 { print!(","); }
        print!("{}", cc[i]);
    }
    println!("]}}");
}

fn gen_case(rng: &mut Rng, mode: usize, t: usize) {
    // Choose m, n based on mode
    let (m, n) = match mode {
        0 => (1usize, 1usize),
        1 => (1, rng.gen_range_usize(1, 100)),
        2 => (rng.gen_range_usize(1, 100), 1),
        3 => (100_000, 1),
        4 => (1, 100_000),
        5 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),
        6 => (rng.gen_range_usize(50, 200), rng.gen_range_usize(50, 200)),
        7 => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
        8 => {
            // Large equal m, n
            let s = rng.gen_range_usize(500, 1000);
            (s, s)
        }
        9 => (rng.gen_range_usize(1, 20), rng.gen_range_usize(1, 20)),
        _ => (rng.gen_range_usize(1, 100), rng.gen_range_usize(1, 100)),
    };

    let cost_mode = (t / 11) % 5;

    let row_costs = make_costs(rng, m, cost_mode);
    let col_costs = make_costs(rng, n, cost_mode);

    // Position selection
    let (sr, sc, hr, hc) = match mode % 4 {
        0 => {
            // same position
            let r = rng.gen_range_usize(0, m - 1);
            let c = rng.gen_range_usize(0, n - 1);
            (r, c, r, c)
        }
        1 => {
            // corners
            (0usize, 0usize, m - 1, n - 1)
        }
        2 => {
            // corners reversed
            (m - 1, n - 1, 0usize, 0usize)
        }
        _ => {
            let sr = rng.gen_range_usize(0, m - 1);
            let sc = rng.gen_range_usize(0, n - 1);
            let hr = rng.gen_range_usize(0, m - 1);
            let hc = rng.gen_range_usize(0, n - 1);
            (sr, sc, hr, hc)
        }
    };

    let (sp, hp, rc, cc) = generate_test_case(m, n, sr, sc, hr, hc, row_costs, col_costs);
    print_json(&sp, &hp, &rc, &cc);
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
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        gen_case(&mut rng, mode, t);
    }
}