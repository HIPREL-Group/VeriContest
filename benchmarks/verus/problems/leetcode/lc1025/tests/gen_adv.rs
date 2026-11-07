use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: i32, delta: i32) -> (n: i32)
    requires
        1 <= base <= 1000,
        0 <= delta,
        base + delta <= 1000,
    ensures
        1 <= n <= 1000,
{
    let n0 = base + delta;
    assert(1 <= n0);
    assert(n0 <= 1000);
    n0
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn adversarial_case(mode: usize, idx: usize, rng: &mut Rng) -> i32 {
    match mode {
        0 => 1,
        1 => 1000,
        2 => {
            if idx % 2 == 0 { 2 } else { 3 }
        }
        3 => {
            let k = (idx % 20) as i32;
            1 + k
        }
        4 => {
            let k = (idx % 20) as i32;
            981 + k
        }
        5 => {
            let vals = [4, 6, 8, 10, 12, 16, 18, 20, 24, 30];
            vals[idx % vals.len()]
        }
        6 => {
            let vals = [1, 3, 5, 7, 9, 11, 15, 21, 27, 999];
            vals[idx % vals.len()]
        }
        7 => {
            let vals = [997, 991, 983, 977, 971, 967, 953, 947];
            vals[idx % vals.len()]
        }
        8 => {
            let vals = [512, 256, 128, 64, 32, 16, 8, 4, 2];
            vals[idx % vals.len()]
        }
        9 => {
            let vals = [999, 998, 500, 501, 750, 251, 840, 841, 625, 624];
            vals[idx % vals.len()]
        }
        _ => rng.gen_range_i32(1, 1000),
    }
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total_cases: usize = 200;
    let adversarial_modes: usize = 10;

    for i in 0..total_cases {
        let n = if i < 120 {
            let mode = i % adversarial_modes;
            adversarial_case(mode, i / adversarial_modes, &mut rng)
        } else {
            let strategy = (rng.next_u64() % 6) as usize;
            match strategy {
                0 => {
                    let base = rng.gen_range_i32(1, 1000);
                    generate_test_case(base, 0)
                }
                1 => {
                    let base = 1;
                    let delta = rng.gen_range_i32(0, 999);
                    generate_test_case(base, delta)
                }
                2 => {
                    let base = rng.gen_range_i32(1, 500);
                    let delta = rng.gen_range_i32(0, 1000 - base);
                    generate_test_case(base, delta)
                }
                3 => {
                    let even = 2 * rng.gen_range_i32(1, 500);
                    generate_test_case(even, 0)
                }
                4 => {
                    let odd = 2 * rng.gen_range_i32(0, 499) + 1;
                    generate_test_case(odd, 0)
                }
                _ => rng.gen_range_i32(1, 1000),
            }
        };

        writeln!(out, "{{\"n\": {}}}", n).unwrap();
    }
}