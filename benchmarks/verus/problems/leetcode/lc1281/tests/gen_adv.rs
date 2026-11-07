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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 100000,
        2 => rng.gen_range_i32(1, 9),
        3 => rng.gen_range_i32(10, 99),
        4 => rng.gen_range_i32(100, 999),
        5 => rng.gen_range_i32(1000, 9999),
        6 => rng.gen_range_i32(10000, 99999),
        7 => {
            // numbers containing a zero digit
            let digits_count = rng.gen_range_i32(2, 5);
            let mut n: i32 = rng.gen_range_i32(1, 9);
            let zero_pos = rng.gen_range_i32(1, digits_count - 1);
            for i in 1..digits_count {
                if i == zero_pos {
                    n = n * 10;
                } else {
                    n = n * 10 + rng.gen_range_i32(1, 9);
                }
            }
            if n < 1 { 1 } else if n > 100000 { 100000 } else { n }
        }
        8 => {
            // repeated digit numbers
            let d = rng.gen_range_i32(1, 9);
            let len = rng.gen_range_i32(1, 5);
            let mut n: i32 = 0;
            for _ in 0..len {
                n = n * 10 + d;
            }
            if n < 1 { 1 } else if n > 100000 { 100000 } else { n }
        }
        9 => {
            // powers of 10
            let p = rng.gen_range_i32(0, 5);
            let mut n: i32 = 1;
            for _ in 0..p {
                n *= 10;
            }
            n
        }
        _ => rng.gen_range_i32(1, 100000),
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let mut n = pick_for_mode(&mut rng, mode);
        if n < 1 { n = 1; }
        if n > 100000 { n = 100000; }
        let val = generate_test_case(n);
        println!("{{\"n\":{}}}", val);
    }
}