use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        2 <= n <= 1000,
        n % 2 == 0,
    ensures
        2 <= res <= 1000,
        res % 2 == 0,
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
    fn gen_even(&mut self, lo: i32, hi: i32) -> i32 {
        // returns even in [lo, hi], lo and hi even
        let span = ((hi - lo) / 2 + 1) as u64;
        let v = self.next_u64() % span;
        lo + (v as i32) * 2
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

    let mut cases: Vec<i32> = Vec::new();

    // Adversarial: boundary values
    cases.push(2);
    cases.push(4);
    cases.push(6);
    cases.push(8);
    cases.push(10);
    cases.push(1000);
    cases.push(998);
    cases.push(996);
    cases.push(994);
    cases.push(992);

    // Known interesting values (powers of 2 minus something, etc.)
    let interesting: [i32; 20] = [12, 16, 20, 24, 30, 32, 50, 64, 100, 128, 200, 256, 300, 500, 512, 600, 700, 800, 900, 950];
    for &v in interesting.iter() {
        cases.push(v);
    }

    // All small evens
    let mut v = 2;
    while v <= 50 {
        cases.push(v);
        v += 2;
    }

    // Random fill to ~200
    while cases.len() < 200 {
        let n = rng.gen_even(2, 1000);
        cases.push(n);
    }

    for n in cases.iter() {
        let res = generate_test_case(*n);
        println!("{{\"n\": {}}}", res);
    }
}