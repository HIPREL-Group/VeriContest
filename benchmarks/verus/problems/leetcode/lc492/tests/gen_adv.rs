use vstd::prelude::*;

verus! {

pub fn generate_test_case(area: i32) -> (res: i32)
    requires
        1 <= area <= 10_000_000,
    ensures
        1 <= res <= 10_000_000,
{
    area
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

fn pick_area(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 4,
        3 => 37,
        4 => 122122,
        5 => 10_000_000,
        6 => 9_999_991, // prime near max
        7 => {
            // perfect square
            let r = rng.gen_range_i32(1, 3162);
            r * r
        }
        8 => {
            // prime-ish -> forces W=1
            let primes = [3, 5, 7, 11, 13, 17, 19, 23, 101, 103, 9973, 99991, 999983];
            primes[(rng.next_u64() as usize) % primes.len()]
        }
        9 => {
            // product of two close factors
            let a = rng.gen_range_i32(2, 3000);
            let b = a + rng.gen_range_i32(0, 5);
            let p = a as i64 * b as i64;
            if p > 10_000_000 { 10_000_000 } else { p as i32 }
        }
        10 => {
            // power of 2
            let exps = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608];
            exps[(rng.next_u64() as usize) % exps.len()]
        }
        _ => rng.gen_range_i32(1, 10_000_000),
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let area = pick_area(&mut rng, mode);
        let area = if area < 1 { 1 } else if area > 10_000_000 { 10_000_000 } else { area };
        let v = generate_test_case(area);
        println!("{{\"area\":{}}}", v);
    }
}