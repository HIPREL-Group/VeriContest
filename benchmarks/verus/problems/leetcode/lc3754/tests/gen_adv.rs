use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        0 <= n <= 1_000_000_000,
    ensures
        0 <= res <= 1_000_000_000,
{
    n
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => rng.gen_range_i64(1, 9) as i32,
        2 => {
            // all zeros except leading: powers of 10
            let e = rng.gen_range_i64(1, 9) as u32;
            10i64.pow(e) as i32
        }
        3 => {
            // digits 1..9 no zeros
            let d = rng.gen_range_i64(1, 9) as i32;
            let len = rng.gen_range_i64(1, 9) as u32;
            let mut v: i64 = 0;
            for _ in 0..len {
                v = v * 10 + d as i64;
                if v > 1_000_000_000 {
                    v /= 10;
                    break;
                }
            }
            v as i32
        }
        4 => 1_000_000_000,
        5 => 999_999_999,
        6 => {
            // lots of zeros
            let a = rng.gen_range_i64(1, 9);
            let b = rng.gen_range_i64(1, 9);
            (a * 100_000_000 + b) as i32
        }
        7 => {
            // sequential digits
            let vals = [12, 123, 1234, 12345, 123456, 1234567, 12345678, 123456789];
            vals[(rng.next_u64() as usize) % vals.len()]
        }
        8 => {
            // alternating zeros
            let vals: [i64; 6] = [10203040, 10203004, 100200300, 506070809, 102030405, 90807060];
            vals[(rng.next_u64() as usize) % vals.len()] as i32
        }
        9 => {
            // random in full range
            rng.gen_range_i64(0, 1_000_000_000) as i32
        }
        _ => rng.gen_range_i64(0, 1000) as i32,
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let mut v = pick_for_mode(&mut rng, mode);
        if v < 0 {
            v = 0;
        }
        if v > 1_000_000_000 {
            v = 1_000_000_000;
        }
        let n = generate_test_case(v);
        println!("{{\"n\": {}}}", n);
    }
}