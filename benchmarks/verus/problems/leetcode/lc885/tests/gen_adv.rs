use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: i32,
    cols: i32,
    r_start: i32,
    c_start: i32,
) -> (res: (i32, i32, i32, i32))
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        0 <= r_start < rows,
        0 <= c_start < cols,
    ensures
        ({
            let (a, b, c, d) = res;
            1 <= a <= 100
            && 1 <= b <= 100
            && 0 <= c < a
            && 0 <= d < b
        }),
{
    (rows, cols, r_start, c_start)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32) {
    match mode {
        0 => {
            // minimal
            (1, 1, 0, 0)
        }
        1 => {
            // 1 x cols, starting at 0,0
            let c = rng.gen_range_i32(1, 100);
            (1, c, 0, 0)
        }
        2 => {
            // rows x 1
            let r = rng.gen_range_i32(1, 100);
            let rs = rng.gen_range_i32(0, r - 1);
            (r, 1, rs, 0)
        }
        3 => {
            // max size, center start
            (100, 100, 50, 50)
        }
        4 => {
            // max size, corner start
            (100, 100, 0, 0)
        }
        5 => {
            // max size, opposite corner
            (100, 100, 99, 99)
        }
        6 => {
            // 1 x 1
            (1, 1, 0, 0)
        }
        7 => {
            // small square
            let n = rng.gen_range_i32(2, 10);
            let rs = rng.gen_range_i32(0, n - 1);
            let cs = rng.gen_range_i32(0, n - 1);
            (n, n, rs, cs)
        }
        8 => {
            // start on edge
            let r = rng.gen_range_i32(2, 50);
            let c = rng.gen_range_i32(2, 50);
            (r, c, 0, rng.gen_range_i32(0, c - 1))
        }
        9 => {
            // start at bottom-right-ish
            let r = rng.gen_range_i32(2, 50);
            let c = rng.gen_range_i32(2, 50);
            (r, c, r - 1, c - 1)
        }
        _ => {
            let r = rng.gen_range_i32(1, 100);
            let c = rng.gen_range_i32(1, 100);
            let rs = rng.gen_range_i32(0, r - 1);
            let cs = rng.gen_range_i32(0, c - 1);
            (r, c, rs, cs)
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
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (a, b, c, d) = pick(&mut rng, mode);
        let (ra, ca, rs, cs) = generate_test_case(a, b, c, d);
        println!("{{\"rows\":{},\"cols\":{},\"r_start\":{},\"c_start\":{}}}", ra, ca, rs, cs);
    }
}