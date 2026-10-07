use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, k: i32) -> (result: (i32, i32))
    ensures
        1 <= result.0 <= 50,
        1 <= result.1 <= 50,
{
    let n = if n < 1 { 1 } else if n > 50 { 50 } else { n };
    let k = if k < 1 { 1 } else if k > 50 { 50 } else { k };
    (n, k)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (50, 50),
        2 => (1, 50),
        3 => (50, 1),
        4 => {
            // n == k/2 boundary
            let k = rng.gen_range_i32(2, 50);
            let n = (k / 2).max(1);
            (n, k)
        }
        5 => {
            // n just above k/2
            let k = rng.gen_range_i32(2, 50);
            let n = ((k / 2) + 1).min(50);
            (n, k)
        }
        6 => {
            // small k, n large
            let k = rng.gen_range_i32(1, 4);
            let n = rng.gen_range_i32(40, 50);
            (n, k)
        }
        7 => {
            // k odd
            let k = 2 * rng.gen_range_i32(1, 24) + 1;
            let n = rng.gen_range_i32(1, 50);
            (n, k)
        }
        8 => {
            // k even
            let k = 2 * rng.gen_range_i32(1, 25);
            let n = rng.gen_range_i32(1, 50);
            (n, k)
        }
        9 => {
            // n == 1
            let k = rng.gen_range_i32(1, 50);
            (1, k)
        }
        _ => {
            let n = rng.gen_range_i32(1, 50);
            let k = rng.gen_range_i32(1, 50);
            (n, k)
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k) = pick_case(&mut rng, mode);
        let (vn, vk) = generate_test_case(n, k);
        println!("{{\"n\": {}, \"k\": {}}}", vn, vk);
    }
}
