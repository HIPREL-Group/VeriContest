use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    length: i32,
    width: i32,
    height: i32,
    mass: i32,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= length <= 100000,
        1 <= width <= 100000,
        1 <= height <= 100000,
        1 <= mass <= 1000,
    ensures
        1 <= result.0 <= 100000,
        1 <= result.1 <= 100000,
        1 <= result.2 <= 100000,
        1 <= result.3 <= 1000,
        result.0 == length,
        result.1 == width,
        result.2 == height,
        result.3 == mass,
{
    (length, width, height, mass)
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

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn clamp_dim(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 100000 { 100000 } else { v }
}

fn clamp_mass(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1000 { 1000 } else { v }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32) {
    // Adversarial modes exploring boundaries of "Bulky"/"Heavy" categorization.
    match mode {
        0 => {
            // random small, light
            (rng.gen_i32(1, 100), rng.gen_i32(1, 100), rng.gen_i32(1, 100), rng.gen_i32(1, 99))
        }
        1 => {
            // random small, heavy
            (rng.gen_i32(1, 100), rng.gen_i32(1, 100), rng.gen_i32(1, 100), rng.gen_i32(100, 1000))
        }
        2 => {
            // exactly one dimension bulky (=10000)
            let pick = rng.next_u64() % 3;
            let dims = if pick == 0 {
                (10000, rng.gen_i32(1, 100), rng.gen_i32(1, 100))
            } else if pick == 1 {
                (rng.gen_i32(1, 100), 10000, rng.gen_i32(1, 100))
            } else {
                (rng.gen_i32(1, 100), rng.gen_i32(1, 100), 10000)
            };
            (dims.0, dims.1, dims.2, rng.gen_i32(1, 1000))
        }
        3 => {
            // dimension just below 10000, volume small
            (9999, 9999, 1, rng.gen_i32(1, 1000))
        }
        4 => {
            // volume exactly >= 1e9 via cube root-ish
            let a = 1000;
            let b = 1000;
            let c = 1000;
            (a, b, c, rng.gen_i32(1, 1000))
        }
        5 => {
            // volume just under 1e9
            (999, 1000, 1000, rng.gen_i32(1, 1000))
        }
        6 => {
            // volume just over 1e9 with small dims
            (1001, 1000, 1000, rng.gen_i32(1, 1000))
        }
        7 => {
            // mass boundary
            let m = if rng.next_u64() % 2 == 0 { 99 } else { 100 };
            (rng.gen_i32(1, 500), rng.gen_i32(1, 500), rng.gen_i32(1, 500), m)
        }
        8 => {
            // max everything
            (100000, 100000, 100000, 1000)
        }
        9 => {
            // min everything
            (1, 1, 1, 1)
        }
        10 => {
            // bulky by dim >= 10000 large, heavy
            (rng.gen_i32(10000, 100000), rng.gen_i32(1, 100000), rng.gen_i32(1, 100000), rng.gen_i32(100, 1000))
        }
        _ => {
            (rng.gen_i32(1, 100000), rng.gen_i32(1, 100000), rng.gen_i32(1, 100000), rng.gen_i32(1, 1000))
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (l, w, h, m) = pick_case(&mut rng, mode);
        let l = clamp_dim(l);
        let w = clamp_dim(w);
        let h = clamp_dim(h);
        let m = clamp_mass(m);
        let (ll, ww, hh, mm) = generate_test_case(l, w, h, m);
        println!("{{\"length\": {}, \"width\": {}, \"height\": {}, \"mass\": {}}}", ll, ww, hh, mm);
    }
}