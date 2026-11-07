use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32) -> (res: i32)
    ensures
        i32::MIN <= res <= i32::MAX,
{
    x
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
        (lo as i64 + (self.next_u64() % span) as i64) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => i32::MAX,
        2 => i32::MIN,
        3 => {
            let candidates = [1i32, -1, 10, -10, 123, -123, 120, -120];
            candidates[(rng.next_u64() as usize) % candidates.len()]
        }
        4 => {
            // Values whose reversal overflows i32, e.g. 1534236469 -> 9646324351
            if rng.next_u64() % 2 == 0 {
                rng.gen_range_i32(1_000_000_000, i32::MAX)
            } else {
                rng.gen_range_i32(i32::MIN, -1_000_000_000)
            }
        }
        5 => {
            // Reversal just inside the range, e.g. 1463847412 -> 2147483641
            let candidates = [1463847412i32, -1463847412, 1463847413, -2147483412, 1563847412];
            candidates[(rng.next_u64() as usize) % candidates.len()]
        }
        6 => {
            // Palindromic numbers
            let candidates = [121i32, 1221, 12321, 1234321, 123454321, -121, -12321];
            candidates[(rng.next_u64() as usize) % candidates.len()]
        }
        7 => {
            // Trailing zeros
            let v = rng.gen_range_i32(-100_000, 100_000);
            v * 1000
        }
        8 => {
            // Powers of 10
            let pows = [1i32, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000];
            let p = pows[(rng.next_u64() as usize) % pows.len()];
            if rng.next_u64() % 2 == 0 { p } else { -p }
        }
        9 => {
            // Small values
            rng.gen_range_i32(-100, 100)
        }
        10 => {
            // Medium values
            rng.gen_range_i32(-1_000_000, 1_000_000)
        }
        11 => {
            // Near the upper boundary
            rng.gen_range_i32(i32::MAX - 100, i32::MAX)
        }
        12 => {
            // Near the lower boundary
            rng.gen_range_i32(i32::MIN, i32::MIN + 100)
        }
        _ => {
            rng.gen_range_i32(i32::MIN, i32::MAX)
        }
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
    let modes = 14usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let x = pick_for_mode(&mut rng, mode);
        let val = generate_test_case(x);
        println!("{{\"x\": {}}}", val);
    }
}