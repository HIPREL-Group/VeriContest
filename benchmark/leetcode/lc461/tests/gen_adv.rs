use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32, y: i32) -> (res: (i32, i32))
    requires
        0 <= x <= i32::MAX,
        0 <= y <= i32::MAX,
    ensures
        0 <= res.0 <= i32::MAX,
        0 <= res.1 <= i32::MAX,
{
    (x, y)
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

    fn gen_i32_nonneg(&mut self) -> i32 {
        let v = self.next_u64();
        (v % (i32::MAX as u64 + 1)) as i32
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn pick_pair(rng: &mut Rng, mode: usize) -> (i32, i32) {
    let max = i32::MAX;
    match mode {
        0 => (0, 0),
        1 => (max, max),
        2 => (0, max),
        3 => (max, 0),
        4 => (1, 4),
        5 => (3, 1),
        6 => {
            let v = rng.gen_range_i32(0, 1000);
            (v, v)
        }
        7 => {
            // one bit difference
            let bit = rng.gen_range_i32(0, 30);
            let base = rng.gen_range_i32(0, max);
            let flipped = base ^ (1i32 << bit);
            (base, flipped.abs())
        }
        8 => {
            // all bits different up to 2^30
            let a = rng.gen_range_i32(0, (1 << 30) - 1);
            let b = a ^ ((1i32 << 30) - 1);
            (a, b)
        }
        9 => {
            let a = rng.gen_i32_nonneg();
            (a, a)
        }
        10 => {
            let a = rng.gen_range_i32(0, 255);
            let b = rng.gen_range_i32(0, 255);
            (a, b)
        }
        _ => {
            let a = rng.gen_i32_nonneg();
            let b = rng.gen_i32_nonneg();
            (a, b)
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
        let mode = if t < modes { t } else { (rng.next_u64() as usize) % modes };
        let (x, y) = pick_pair(&mut rng, mode);
        let x = if x < 0 { 0 } else { x };
        let y = if y < 0 { 0 } else { y };
        let (xo, yo) = generate_test_case(x, y);
        println!("{{\"x\": {}, \"y\": {}}}", xo, yo);
    }
}