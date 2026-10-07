use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: u32) -> (res: u32)
    ensures
        0 <= res <= u32::MAX,
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

    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        let span = (hi as u64) - (lo as u64) + 1;
        lo + ((self.next_u64() % span) as u32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> u32 {
    match mode {
        0 => 0,
        1 => u32::MAX,
        2 => 1,
        3 => 10,
        4 => 123,
        5 => 120,
        6 => {
            // Values whose reversal would overflow u32
            // u32::MAX = 4294967295, reversed is 5927694924 which is > u32::MAX
            rng.gen_range_u32(1_000_000_000, u32::MAX)
        }
        7 => {
            // Palindromic numbers
            let candidates = [121u32, 1221, 12321, 1234321, 123454321, 1];
            candidates[(rng.next_u64() as usize) % candidates.len()]
        }
        8 => {
            // Trailing zeros
            let v = rng.gen_range_u32(1, 100_000);
            v * 1000
        }
        9 => {
            // Powers of 10
            let pows = [1u32, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000];
            pows[(rng.next_u64() as usize) % pows.len()]
        }
        10 => {
            // Small values
            rng.gen_range_u32(0, 100)
        }
        11 => {
            // Medium values
            rng.gen_range_u32(100, 1_000_000)
        }
        12 => {
            // Near boundary
            rng.gen_range_u32(u32::MAX - 100, u32::MAX)
        }
        _ => {
            rng.gen_range_u32(0, u32::MAX)
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