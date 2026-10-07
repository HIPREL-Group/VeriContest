use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, m: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 100000,
        1 <= m <= 100000,
    ensures
        1 <= result.0 <= 100000,
        1 <= result.1 <= 100000,
{
    (n, m)
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1, 100000),
        2 => (100000, 1),
        3 => (100000, 100000),
        4 => {
            let n = rng.gen_range_i32(1, 10);
            let m = rng.gen_range_i32(1, 10);
            (n, m)
        }
        5 => {
            let n = rng.gen_range_i32(1, 100000);
            (n, n)
        }
        6 => {
            let n = rng.gen_range_i32(1, 100000);
            let m = rng.gen_range_i32(1, 100000);
            (n, m)
        }
        7 => {
            // both odd
            let n = 2 * rng.gen_range_i32(0, 49999) + 1;
            let m = 2 * rng.gen_range_i32(0, 49999) + 1;
            (n, m)
        }
        8 => {
            // both even
            let n = 2 * rng.gen_range_i32(1, 50000);
            let m = 2 * rng.gen_range_i32(1, 50000);
            (n, m)
        }
        9 => {
            // one odd, one even
            let n = 2 * rng.gen_range_i32(1, 50000);
            let m = 2 * rng.gen_range_i32(0, 49999) + 1;
            (n, m)
        }
        _ => {
            let base = (t as i32) % 100000 + 1;
            let other = ((t * 7) as i32) % 100000 + 1;
            (base, other)
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
        let (n, m) = pick_for_mode(&mut rng, mode, t);
        let (nn, mm) = generate_test_case(n, m);
        println!("{{\"n\": {}, \"m\": {}}}", nn, mm);
    }
}