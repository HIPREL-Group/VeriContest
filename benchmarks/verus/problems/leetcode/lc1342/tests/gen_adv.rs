use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        0 <= n <= 1_000_000,
    ensures
        0 <= result <= 1_000_000,
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

fn pick_value(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 1_000_000,
        4 => 999_999,
        5 => {
            // power of two
            let exps = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288];
            let idx = (rng.next_u64() as usize) % exps.len();
            exps[idx] as i32
        }
        6 => {
            // power of two minus 1
            let exps = [1, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047, 4095, 8191, 16383, 32767, 65535, 131071, 262143, 524287];
            let idx = (rng.next_u64() as usize) % exps.len();
            exps[idx] as i32
        }
        7 => rng.gen_range_i32(0, 100),
        8 => rng.gen_range_i32(0, 1000),
        9 => rng.gen_range_i32(900_000, 1_000_000),
        _ => rng.gen_range_i32(0, 1_000_000),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let v = pick_value(&mut rng, mode);
        let result = generate_test_case(v);
        println!("{{\"num\": {}}}", result);
    }
}