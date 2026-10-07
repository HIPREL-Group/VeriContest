use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 100_000_000,
    ensures
        1 <= res <= 100_000_000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
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
    
    // Known perfect numbers up to 10^8: 6, 28, 496, 8128, 33550336
    let known_perfect: [i32; 5] = [6, 28, 496, 8128, 33550336];
    
    let mut outputs: Vec<i32> = Vec::new();
    
    // Adversarial: known perfect numbers
    for &p in known_perfect.iter() {
        outputs.push(p);
    }
    
    // Adversarial: near perfect numbers
    for &p in known_perfect.iter() {
        if p > 1 { outputs.push(p - 1); }
        if p < 100_000_000 { outputs.push(p + 1); }
    }
    
    // Edge cases
    outputs.push(1);
    outputs.push(2);
    outputs.push(3);
    outputs.push(4);
    outputs.push(5);
    outputs.push(7);
    outputs.push(100_000_000);
    outputs.push(99_999_999);
    
    // Powers of 2 (near-perfect: sum of divisors = n-1)
    let mut p: i32 = 2;
    while p <= 100_000_000 / 2 {
        outputs.push(p);
        if p > i32::MAX / 2 { break; }
        p = p * 2;
    }
    
    // Primes-ish, small values
    for i in 1..50 {
        outputs.push(i);
    }
    
    // Multiples of small perfect numbers
    for k in 2..20 {
        outputs.push(6 * k);
        outputs.push(28 * k);
    }
    
    // Random values
    while outputs.len() < 200 {
        let mode = rng.next_u64() % 5;
        let v = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => rng.gen_range_i32(1, 10_000),
            2 => rng.gen_range_i32(1, 1_000_000),
            3 => rng.gen_range_i32(1, 100_000_000),
            _ => rng.gen_range_i32(99_000_000, 100_000_000),
        };
        outputs.push(v);
    }
    
    for v in outputs.iter() {
        let n = generate_test_case(*v);
        println!("{{\"num\": {}}}", n);
    }
}