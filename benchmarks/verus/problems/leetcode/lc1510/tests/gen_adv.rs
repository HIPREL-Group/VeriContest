use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= 100000,
    ensures
        1 <= res <= 100000,
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

    // Adversarial fixed cases
    let mut cases: Vec<i32> = Vec::new();

    // Small edge cases
    for k in 1..=30 {
        cases.push(k);
    }
    // Perfect squares
    let squares = [1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225,
                   256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729,
                   784, 841, 900, 961, 1024, 10000, 99856, 99225];
    for &s in squares.iter() {
        cases.push(s);
    }
    // Squares plus/minus 1
    for &s in squares.iter() {
        if s + 1 <= 100000 { cases.push(s + 1); }
        if s - 1 >= 1 { cases.push(s - 1); }
    }
    // Boundary
    cases.push(100000);
    cases.push(99999);
    cases.push(99998);
    cases.push(99997);
    cases.push(1);
    cases.push(2);
    cases.push(3);

    // Near upper boundary
    for k in 0..30 {
        cases.push(100000 - k);
    }

    // Known losing positions (Alice loses) from classical analysis:
    // 2, 5, 7, 10, 12, 15, 17, 20, 22, ...
    let losing = [2, 5, 7, 10, 12, 15, 17, 20, 22, 34, 39, 44];
    for &l in losing.iter() {
        cases.push(l);
    }

    // Fill with random cases up to ~200
    while cases.len() < 220 {
        let mode = rng.next_u64() % 5;
        let v = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => rng.gen_range_i32(1, 1000),
            2 => rng.gen_range_i32(1, 10000),
            3 => rng.gen_range_i32(1, 100000),
            _ => rng.gen_range_i32(99000, 100000),
        };
        cases.push(v);
    }

    for &c in cases.iter() {
        let n = generate_test_case(c);
        println!("{{\"n\": {}}}", n);
    }
}