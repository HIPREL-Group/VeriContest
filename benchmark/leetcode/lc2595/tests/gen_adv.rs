use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, div: i32) -> (result: (i32, i32))
    requires
        1 <= n <= 1000,
        1 <= div <= 1024,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1024,
{
    (n, div)
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

fn pick_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1024),
        2 => (1000, 1),
        3 => (1, 1024),
        4 => {
            // Powers of 2
            let powers = [1i32, 2, 4, 8, 16, 32, 64, 128, 256, 512];
            let p = powers[t % powers.len()];
            (p, 1)
        }
        5 => {
            // All bits set values
            let vals = [1i32, 3, 7, 15, 31, 63, 127, 255, 511, 1023];
            let v = vals[t % vals.len()];
            (v.min(1000), 1)
        }
        6 => {
            // Only even bits
            let vals = [1i32, 5, 21, 85, 341];
            let v = vals[t % vals.len()];
            (v.min(1000), 1)
        }
        7 => {
            // Only odd bits
            let vals = [2i32, 10, 42, 170, 682];
            let v = vals[t % vals.len()];
            (v.min(1000), 1)
        }
        8 => {
            // Example values
            let vals = [50i32, 2, 17, 100, 999, 500];
            let v = vals[t % vals.len()];
            (v, 1)
        }
        9 => {
            // Divisor variations
            let divs = [1i32, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024];
            let d = divs[t % divs.len()];
            (rng.gen_range_i32(1, 1000), d)
        }
        _ => {
            (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1024))
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, div) = pick_case(&mut rng, mode, t);
        let (out_n, out_div) = generate_test_case(n, div);
        println!("{{\"n\":{},\"div\":{}}}", out_n, out_div);
    }
}