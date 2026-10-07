use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, d_val: i32) -> (result: (i32, i32))
    requires
        100 <= n_val <= 999,
        0 <= d_val <= 9,
    ensures
        ({
            let (num, d) = result;
            100 <= num <= 999 && 0 <= d <= 9 && num == n_val && d == d_val
        }),
{
    (n_val, d_val)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
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

fn pick_test(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (192, rng.gen_range_i32(0, 9)),
        1 => (100, rng.gen_range_i32(0, 9)),
        2 => (999, rng.gen_range_i32(0, 9)),
        3 => (101, rng.gen_range_i32(0, 9)),
        4 => (333, rng.gen_range_i32(0, 9)),
        5 => {
            // fascinating candidates: 192, 219, 273, 327
            let cands = [192, 219, 273, 327];
            let i = (rng.next_u64() as usize) % cands.len();
            (cands[i], rng.gen_range_i32(0, 9))
        }
        6 => (rng.gen_range_i32(100, 333), rng.gen_range_i32(0, 9)),
        7 => (rng.gen_range_i32(334, 999), rng.gen_range_i32(0, 9)),
        8 => (rng.gen_range_i32(100, 999), 0),
        9 => (rng.gen_range_i32(100, 999), 9),
        _ => (rng.gen_range_i32(100, 999), rng.gen_range_i32(0, 9)),
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
        let (nv, dv) = pick_test(&mut rng, mode);
        let (num, _d) = generate_test_case(nv, dv);
        println!("{{\"n\":{}}}", num);
    }
}