use vstd::prelude::*;

verus! {

pub fn generate_test_case(num: i32, k: i32) -> (result: (i32, i32))
    requires
        0 <= num <= 3000,
        0 <= k <= 9,
    ensures
        0 <= result.0 <= 3000,
        0 <= result.1 <= 9,
        result.0 == num,
        result.1 == k,
{
    (num, k)
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

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, rng.gen_range_i32(0, 9)),
        1 => (rng.gen_range_i32(0, 3000), 0),
        2 => (rng.gen_range_i32(0, 3000), rng.gen_range_i32(0, 9)),
        3 => (rng.gen_range_i32(0, 9), rng.gen_range_i32(0, 9)),
        4 => (3000, rng.gen_range_i32(0, 9)),
        5 => (rng.gen_range_i32(0, 3000), 9),
        6 => (rng.gen_range_i32(0, 3000), 5),
        7 => {
            let k = rng.gen_range_i32(1, 9);
            let c = rng.gen_range_i32(1, 10);
            (k * c, k)
        }
        8 => (rng.gen_range_i32(1, 50), rng.gen_range_i32(0, 9)),
        9 => (37, 2),
        _ => (rng.gen_range_i32(0, 3000), rng.gen_range_i32(0, 9)),
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
        let (num, k) = pick(&mut rng, mode);
        let (n, kk) = generate_test_case(num, k);
        println!("{{\"num\": {}, \"k\": {}}}", n, kk);
    }
}