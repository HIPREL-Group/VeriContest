use vstd::prelude::*;

verus! {

pub fn generate_test_case(value: i64) -> (result: i64)
    requires
        1 <= value <= 1_000_000_000_000_000i64,
    ensures
        1 <= result <= 1_000_000_000_000_000i64,
{
    value
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn apples_at(r: i64) -> i128 {
    2i128 * (r as i128) * (r as i128 + 1) * (2 * r as i128 + 1)
}

fn adversarial_boundary(r: i64, offset: i64) -> i64 {
    // Pick needed_apples close to apples(r)
    let a = apples_at(r);
    let candidate = a + offset as i128;
    if candidate < 1 {
        1
    } else if candidate > 1_000_000_000_000_000i128 {
        1_000_000_000_000_000i64
    } else {
        candidate as i64
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let value: i64 = match mode {
            0 => {
                // small values
                rng.gen_range_i64(1, 100)
            }
            1 => {
                // exactly the example values
                match t % 3 {
                    0 => 1,
                    1 => 13,
                    _ => 1_000_000_000,
                }
            }
            2 => {
                // max boundary
                1_000_000_000_000_000i64
            }
            3 => {
                // near max
                rng.gen_range_i64(999_999_000_000_000, 1_000_000_000_000_000)
            }
            4 => {
                // exactly apples(r) for some r
                let r = rng.gen_range_i64(1, 10000);
                let a = apples_at(r);
                if a > 1_000_000_000_000_000i128 { 1_000_000_000_000_000i64 }
                else if a < 1 { 1 }
                else { a as i64 }
            }
            5 => {
                // apples(r) - 1
                let r = rng.gen_range_i64(2, 10000);
                adversarial_boundary(r, -1)
            }
            6 => {
                // apples(r) + 1
                let r = rng.gen_range_i64(1, 10000);
                adversarial_boundary(r, 1)
            }
            7 => {
                // medium random
                rng.gen_range_i64(1, 1_000_000_000)
            }
            8 => {
                // large random
                rng.gen_range_i64(1_000_000_000, 1_000_000_000_000_000)
            }
            9 => {
                // powers of 10
                let p = (t % 16) as u32;
                let mut v: i64 = 1;
                for _ in 0..p {
                    if v <= 100_000_000_000_000 {
                        v *= 10;
                    }
                }
                v
            }
            _ => {
                // fully random
                rng.gen_range_i64(1, 1_000_000_000_000_000)
            }
        };

        let v = generate_test_case(value);
        println!("{{\"needed_apples\":{}}}", v);
    }
}