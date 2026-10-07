use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1000,
    ensures
        1 <= result <= 1000,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1000,
        2 => 3,   // already all-set
        3 => 7,   // already all-set
        4 => 15,  // already all-set
        5 => 31,  // already all-set
        6 => 63,  // already all-set
        7 => 127, // already all-set
        8 => 511, // already all-set
        9 => {
            // one below a power-of-two-minus-1
            let options = [2i32, 4, 8, 16, 32, 64, 128, 256, 512];
            options[(rng.next_u64() as usize) % options.len()]
        }
        10 => {
            // just above a power-of-two-minus-1
            let options = [4i32, 8, 16, 32, 64, 128, 256, 512, 1000];
            let pick = options[(rng.next_u64() as usize) % options.len()];
            if pick == 1000 { 1000 } else { pick }
        }
        11 => {
            // powers of two
            let options = [2i32, 4, 8, 16, 32, 64, 128, 256, 512];
            options[(rng.next_u64() as usize) % options.len()]
        }
        12 => {
            // values near 1023 boundary
            let options = [500i32, 600, 700, 800, 900, 1000, 512, 513, 1023_i32.min(1000)];
            options[(rng.next_u64() as usize) % options.len()]
        }
        _ => rng.gen_range_i32(1, 1000),
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
        let n_raw = pick_for_mode(&mut rng, mode);
        let n = if n_raw < 1 { 1 } else if n_raw > 1000 { 1000 } else { n_raw };
        let out = generate_test_case(n);
        println!("{{\"n\": {}}}", out);
    }
}