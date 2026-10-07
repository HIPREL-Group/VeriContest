use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: i32, offset: i32, use_offset: bool) -> (n: i32)
    requires
        1 <= base <= 10000,
        0 <= offset <= 10000,
        use_offset ==> base + offset <= 10000,
        !use_offset ==> base - offset >= 1,
    ensures
        1 <= n <= 10000,
{
    let n =
        if use_offset {
            base + offset
        } else {
            base - offset
        };
    assert(1 <= n);
    assert(n <= 10000);
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005u64)
            .wrapping_add(1442695040888963407u64);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 0
    }
}

fn make_case(mode: usize, rng: &mut Rng, idx: usize) -> i32 {
    match mode {
        0 => generate_test_case(1, 0, true),
        1 => generate_test_case(10000, 0, false),
        2 => {
            let base = rng.gen_range_i32(1, 10000);
            generate_test_case(base, 0, rng.gen_bool())
        }
        3 => {
            let base = rng.gen_range_i32(1, 32);
            let offset = rng.gen_range_i32(0, 10000 - base);
            generate_test_case(base, offset, true)
        }
        4 => {
            let base = rng.gen_range_i32(9969, 10000);
            let offset = rng.gen_range_i32(0, base - 1);
            generate_test_case(base, offset, false)
        }
        5 => {
            let vals = [1, 2, 3, 4, 5, 6, 7, 8];
            let base = vals[idx % vals.len()];
            let max_up = 10000 - base;
            let offset = if max_up == 0 { 0 } else { rng.gen_range_i32(0, max_up.min(3)) };
            generate_test_case(base, offset, true)
        }
        6 => {
            let vals = [9993, 9994, 9995, 9996, 9997, 9998, 9999, 10000];
            let base = vals[idx % vals.len()];
            let offset = rng.gen_range_i32(0, (base - 1).min(3));
            generate_test_case(base, offset, false)
        }
        7 => {
            let k = rng.gen_range_i32(1, 2500);
            let base = 4 * k;
            let offset = rng.gen_range_i32(0, (10000 - base).min(12));
            generate_test_case(base, offset, true)
        }
        8 => {
            let k = rng.gen_range_i32(1, 2500);
            let base = 4 * k - 1;
            let offset = rng.gen_range_i32(0, (base - 1).min(12));
            generate_test_case(base, offset, false)
        }
        9 => {
            let choose_upper = rng.gen_bool();
            if choose_upper {
                let base = 10000;
                let offset = rng.gen_range_i32(0, 8);
                generate_test_case(base, offset, false)
            } else {
                let base = 1;
                let offset = rng.gen_range_i32(0, 8);
                generate_test_case(base, offset, true)
            }
        }
        _ => {
            let use_offset = rng.gen_bool();
            if use_offset {
                let base = rng.gen_range_i32(1, 10000);
                let offset = rng.gen_range_i32(0, 10000 - base);
                generate_test_case(base, offset, true)
            } else {
                let base = rng.gen_range_i32(1, 10000);
                let offset = rng.gen_range_i32(0, base - 1);
                generate_test_case(base, offset, false)
            }
        }
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

    let total: usize = 200;
    for i in 0..total {
        let mode = if i < 120 {
            i % 10
        } else {
            10
        };
        let n = make_case(mode, &mut rng, i);
        writeln!(out, "{{\"n\": {}}}", n).unwrap();
    }
}