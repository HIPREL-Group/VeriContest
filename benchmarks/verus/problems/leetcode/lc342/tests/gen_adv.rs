use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        -2_147_483_648 <= n <= 2_147_483_647,
    ensures
        -2_147_483_648 <= res <= 2_147_483_647,
        res == n,
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

    fn gen_i32(&mut self) -> i32 {
        self.next_u64() as i32
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn powers_of_four() -> Vec<i32> {
    let mut v = Vec::new();
    let mut x: i64 = 1;
    while x <= i32::MAX as i64 {
        v.push(x as i32);
        x *= 4;
    }
    v
}

fn powers_of_two() -> Vec<i32> {
    let mut v = Vec::new();
    let mut x: i64 = 1;
    while x <= i32::MAX as i64 {
        v.push(x as i32);
        x *= 2;
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let pow4 = powers_of_four();
    let pow2 = powers_of_two();

    let mut tests: Vec<i32> = Vec::new();

    // Mode 0: All powers of four (should return true)
    for &p in &pow4 {
        tests.push(p);
    }

    // Mode 1: Negative powers of four (should return false)
    for &p in &pow4 {
        if p > 0 {
            tests.push(-p);
        }
    }

    // Mode 2: Powers of two that aren't powers of four (2, 8, 32, ...)
    for &p in &pow2 {
        let mut is4 = false;
        for &q in &pow4 {
            if p == q {
                is4 = true;
                break;
            }
        }
        if !is4 {
            tests.push(p);
        }
    }

    // Mode 3: edge values
    tests.push(0);
    tests.push(1);
    tests.push(-1);
    tests.push(i32::MAX);
    tests.push(i32::MIN);
    tests.push(2);
    tests.push(3);
    tests.push(4);
    tests.push(5);
    tests.push(-4);
    tests.push(-16);

    // Mode 4: power of four ± 1
    for &p in &pow4 {
        if p < i32::MAX {
            tests.push(p + 1);
        }
        if p > i32::MIN + 1 {
            tests.push(p - 1);
        }
    }

    // Mode 5: power of four * 3 (has factor 3 so not power of 4)
    for &p in &pow4 {
        if (p as i64) * 3 <= i32::MAX as i64 {
            tests.push(p * 3);
        }
    }

    // Mode 6: random small values
    for _ in 0..40 {
        tests.push(rng.gen_range_i32(-100, 100));
    }

    // Mode 7: random medium values
    for _ in 0..40 {
        tests.push(rng.gen_range_i32(-100000, 100000));
    }

    // Mode 8: fully random i32
    for _ in 0..40 {
        tests.push(rng.gen_i32());
    }

    // Mode 9: multiples of 4 that aren't powers of 4
    for _ in 0..20 {
        let x = rng.gen_range_i32(1, 100000);
        tests.push(x * 4);
    }

    // Pad to ~200+
    while tests.len() < 220 {
        tests.push(rng.gen_i32());
    }

    for &n in &tests {
        let v = generate_test_case(n);
        println!("{{\"n\":{}}}", v);
    }
}