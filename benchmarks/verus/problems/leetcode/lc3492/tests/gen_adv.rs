use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, w: i32, max_weight: i32) -> (result: (i32, i32, i32))
    requires
        1 <= n <= 1000,
        1 <= w <= 1000,
        1 <= max_weight <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
        1 <= result.2 <= 1_000_000_000,
{
    (n, w, max_weight)
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
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn emit(n: i32, w: i32, max_weight: i32) {
    let (a, b, c) = generate_test_case(n, w, max_weight);
    println!("{{\"n\": {}, \"w\": {}, \"max_weight\": {}}}", a, b, c);
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (1, 1, 1),
        1 => (1000, 1000, 1_000_000_000),
        2 => (1000, 1, 1),
        3 => (1, 1000, 1_000_000_000),
        4 => {
            // n*n*w exactly equals maxWeight
            let n = rng.gen_i32(1, 1000);
            let w = rng.gen_i32(1, 1000);
            let mw_candidate = (n as i64) * (n as i64) * (w as i64);
            let mw = if mw_candidate >= 1 && mw_candidate <= 1_000_000_000 {
                mw_candidate as i32
            } else {
                rng.gen_i32(1, 1_000_000_000)
            };
            (n, w, mw)
        }
        5 => {
            // maxWeight just one less than n*n*w
            let n = rng.gen_i32(1, 1000);
            let w = rng.gen_i32(1, 1000);
            let mw_candidate = (n as i64) * (n as i64) * (w as i64) - 1;
            let mw = if mw_candidate >= 1 && mw_candidate <= 1_000_000_000 {
                mw_candidate as i32
            } else {
                rng.gen_i32(1, 1_000_000_000)
            };
            (n, w, mw)
        }
        6 => {
            // tiny deck
            let n = rng.gen_i32(1, 3);
            let w = rng.gen_i32(1, 1000);
            let mw = rng.gen_i32(1, 1_000_000_000);
            (n, w, mw)
        }
        7 => {
            // large deck
            let n = rng.gen_i32(900, 1000);
            let w = rng.gen_i32(1, 1000);
            let mw = rng.gen_i32(1, 1_000_000_000);
            (n, w, mw)
        }
        8 => {
            // max_weight small
            let n = rng.gen_i32(1, 1000);
            let w = rng.gen_i32(1, 1000);
            let mw = rng.gen_i32(1, 100);
            (n, w, mw)
        }
        9 => {
            // max_weight divisible by w
            let w = rng.gen_i32(1, 1000);
            let k = rng.gen_i32(1, 1_000_000);
            let mw_c = (w as i64) * (k as i64);
            let mw = if mw_c >= 1 && mw_c <= 1_000_000_000 { mw_c as i32 } else { w };
            let n = rng.gen_i32(1, 1000);
            (n, w, mw)
        }
        _ => {
            let n = rng.gen_i32(1, 1000);
            let w = rng.gen_i32(1, 1000);
            let mw = rng.gen_i32(1, 1_000_000_000);
            (n, w, mw)
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

    // A few fixed examples
    emit(2, 3, 15);
    emit(3, 5, 20);
    emit(1, 1, 1);
    emit(1000, 1000, 1_000_000_000);
    emit(1000, 1, 1);
    emit(1, 1000, 1000);

    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, w, mw) = pick(&mut rng, mode);
        // clamp to be safe
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let w = if w < 1 { 1 } else if w > 1000 { 1000 } else { w };
        let mw = if mw < 1 { 1 } else if mw > 1_000_000_000 { 1_000_000_000 } else { mw };
        emit(n, w, mw);
    }
}