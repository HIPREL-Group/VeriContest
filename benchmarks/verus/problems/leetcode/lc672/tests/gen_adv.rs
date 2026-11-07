use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, presses_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 1000,
        0 <= presses_val <= 1000,
    ensures
        1 <= result.0 <= 1000,
        0 <= result.1 <= 1000,
{
    (n_val, presses_val)
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32) {
    match mode {
        0 => (1, rng.gen_range_i32(0, 1000)),
        1 => (2, rng.gen_range_i32(0, 1000)),
        2 => (3, rng.gen_range_i32(0, 1000)),
        3 => (rng.gen_range_i32(1, 1000), 0),
        4 => (rng.gen_range_i32(1, 1000), 1),
        5 => (rng.gen_range_i32(1, 1000), 2),
        6 => (rng.gen_range_i32(1, 1000), 3),
        7 => (1000, 1000),
        8 => (1, 1),
        9 => {
            let small_n = [1, 2, 3, 4, 5, 6, 7];
            let small_p = [0, 1, 2, 3, 4, 5];
            let n = small_n[t % small_n.len()];
            let p = small_p[(t / 7) % small_p.len()];
            (n, p)
        }
        _ => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(0, 1000)),
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
        let (n, p) = pick_case(&mut rng, mode, t);
        let (nn, pp) = generate_test_case(n, p);
        println!("{{\"n\": {}, \"presses\": {}}}", nn, pp);
    }
}