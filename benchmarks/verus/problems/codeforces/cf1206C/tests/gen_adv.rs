use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize) -> (res: usize)
    requires
        1 <= n <= 100000,
    ensures
        1 <= res <= 100000,
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

    // Adversarial cases
    let mut cases: Vec<usize> = Vec::new();

    // Edge cases
    cases.push(1);
    cases.push(2);
    cases.push(3);
    cases.push(4);
    cases.push(5);
    cases.push(6);
    cases.push(7);
    cases.push(8);
    cases.push(9);
    cases.push(10);
    cases.push(99999);
    cases.push(100000);
    cases.push(99998);
    cases.push(99997);

    // Small odd values (valid answers exist)
    for k in 0..30 {
        cases.push(2 * k + 1);
    }
    // Small even values (NO answer)
    for k in 1..30 {
        cases.push(2 * k);
    }

    // Powers of 2
    let mut p = 1usize;
    while p <= 100000 {
        cases.push(p);
        if p < 100000 { cases.push(p + 1); }
        if p > 1 { cases.push(p - 1); }
        p *= 2;
    }

    // Powers of 2 minus/plus, odd/even around boundaries
    cases.push(65535);
    cases.push(65536);
    cases.push(65537);
    cases.push(32767);
    cases.push(32768);
    cases.push(32769);

    // Random fill to ~200
    while cases.len() < 200 {
        let mode = rng.gen_range_usize(0, 4);
        let n = match mode {
            0 => rng.gen_range_usize(1, 20),
            1 => rng.gen_range_usize(1, 1000),
            2 => rng.gen_range_usize(1000, 100000),
            3 => {
                // random odd
                let x = rng.gen_range_usize(1, 50000);
                2 * x - 1
            }
            _ => {
                // random even
                let x = rng.gen_range_usize(1, 50000);
                2 * x
            }
        };
        cases.push(n);
    }

    for &n in cases.iter() {
        if n >= 1 && n <= 100000 {
            let v = generate_test_case(n);
            println!("{{\"n\": {}}}", v);
        }
    }
}