use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 10_000_000,
    ensures
        1 <= result <= 10_000_000,
{
    n
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

// Build sum of distinct powers of 3 from a bitmask
fn sum_pow3_mask(mask: u32) -> i64 {
    let mut result: i64 = 0;
    let mut p: i64 = 1;
    let mut m = mask;
    while m > 0 {
        if m & 1 == 1 {
            result += p;
        }
        m >>= 1;
        p *= 3;
        if result > 10_000_000 {
            return -1;
        }
    }
    result
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);

    // Collect powers of 3 up to 10^7
    let mut powers: Vec<i32> = Vec::new();
    let mut p: i64 = 1;
    while p <= 10_000_000 {
        powers.push(p as i32);
        p *= 3;
    }

    let mut outputs: Vec<i32> = Vec::new();

    // Mode 0: boundary values
    outputs.push(1);
    outputs.push(2);
    outputs.push(3);
    outputs.push(4);
    outputs.push(10_000_000);
    outputs.push(9_999_999);
    outputs.push(9_999_998);

    // Mode 1: all powers of 3
    for &pw in &powers {
        outputs.push(pw);
    }

    // Mode 2: powers of 3 minus 1 and plus 1
    for &pw in &powers {
        if pw > 1 {
            outputs.push(pw - 1);
        }
        if (pw as i64) + 1 <= 10_000_000 {
            outputs.push(pw + 1);
        }
    }

    // Mode 3: sums of distinct powers (valid cases) - all bitmasks
    for mask in 1u32..(1u32 << powers.len().min(15)) {
        let s = sum_pow3_mask(mask);
        if s >= 1 && s <= 10_000_000 {
            outputs.push(s as i32);
            if outputs.len() > 60 {
                break;
            }
        }
    }

    // Mode 4: numbers whose base-3 representation contains digit 2 (invalid)
    // e.g. 2, 5, 6, 7, 8, 11, ...
    for i in 0..15 {
        let base: i64 = 3_i64.pow(i);
        let v = 2 * base;
        if v <= 10_000_000 {
            outputs.push(v as i32);
        }
    }

    // Mode 5: random values
    for _ in 0..50 {
        outputs.push(rng.gen_range_i32(1, 10_000_000));
    }

    // Mode 6: small random
    for _ in 0..30 {
        outputs.push(rng.gen_range_i32(1, 100));
    }

    // Mode 7: medium random
    for _ in 0..30 {
        outputs.push(rng.gen_range_i32(100, 100_000));
    }

    // Mode 8: adversarial - numbers near powers
    for &pw in &powers {
        let v = rng.gen_range_i32(-5, 5);
        let cand = pw as i64 + v as i64;
        if cand >= 1 && cand <= 10_000_000 {
            outputs.push(cand as i32);
        }
    }

    // Mode 9: known examples
    outputs.push(12);
    outputs.push(91);
    outputs.push(21);

    // Fill to ~200
    while outputs.len() < 200 {
        outputs.push(rng.gen_range_i32(1, 10_000_000));
    }

    for &n in outputs.iter().take(220) {
        let result = generate_test_case(n);
        println!("{{\"n\": {}}}", result);
    }
}