use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, row: i32, col: i32) -> (res: (i32, i32, i32))
    ensures
        1 <= res.0 <= 20,
        0 <= res.1 < res.0,
        0 <= res.2 < res.0,
{
    let n = if n < 1 { 1 } else if n > 20 { 20 } else { n };
    let row = if row < 0 { 0 } else if row >= n { n - 1 } else { row };
    let col = if col < 0 { 0 } else if col >= n { n - 1 } else { col };
    (n, row, col)
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

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (1, 0, 0),
        1 => (2, 0, 0),
        2 => (2, 1, 1),
        3 => (3, 1, 1),
        4 => (20, 0, 0),
        5 => (20, 19, 19),
        6 => (20, 0, 19),
        7 => (20, 19, 0),
        8 => {
            let n = rng.gen_range_i32(1, 20);
            let r = rng.gen_range_i32(0, n - 1);
            let c = rng.gen_range_i32(0, n - 1);
            (n, r, c)
        }
        9 => {
            let n = rng.gen_range_i32(2, 20);
            let r = rng.gen_range_i32(0, n - 1);
            (n, r, 0)
        }
        10 => {
            let n = rng.gen_range_i32(2, 20);
            let c = rng.gen_range_i32(0, n - 1);
            (n, 0, c)
        }
        11 => {
            let n = rng.gen_range_i32(2, 20);
            let r = rng.gen_range_i32(0, n - 1);
            (n, r, n - 1)
        }
        12 => {
            let n = rng.gen_range_i32(2, 20);
            let c = rng.gen_range_i32(0, n - 1);
            (n, n - 1, c)
        }
        13 => {
            // diagonal
            let n = rng.gen_range_i32(1, 20);
            let d = rng.gen_range_i32(0, n - 1);
            (n, d, d)
        }
        14 => {
            // anti-diagonal
            let n = rng.gen_range_i32(1, 20);
            let d = rng.gen_range_i32(0, n - 1);
            (n, d, n - 1 - d)
        }
        15 => {
            // center-ish for odd n
            let n = 2 * rng.gen_range_i32(1, 9) + 1;
            (n, n / 2, n / 2)
        }
        _ => {
            let n = rng.gen_range_i32(1, 20);
            let r = rng.gen_range_i32(0, n - 1);
            let c = rng.gen_range_i32(0, n - 1);
            (n, r, c)
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
    let modes = 17usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, r, c) = pick_case(&mut rng, mode);
        let (nn, rr, cc) = generate_test_case(n, r, c);
        println!("{{\"n\":{},\"row\":{},\"col\":{}}}", nn, rr, cc);
    }
}
