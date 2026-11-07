use vstd::prelude::*;

verus! {

pub fn generate_test_case(target: i32, max_doubles: i32) -> (result: (i32, i32))
    requires
        1 <= target <= 1_000_000_000,
        0 <= max_doubles <= 100,
    ensures
        1 <= result.0 <= 1_000_000_000,
        0 <= result.1 <= 100,
{
    (target, max_doubles)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 0),
        1 => (1, rng.gen_range_i32(0, 100)),
        2 => (1_000_000_000, 100),
        3 => (1_000_000_000, 0),
        4 => (rng.gen_range_i32(1, 100), 0),
        5 => {
            // power of 2
            let k = rng.gen_range_i32(0, 29);
            let t = 1i32 << k;
            (t, rng.gen_range_i32(0, 100))
        }
        6 => {
            // just below a power of 2
            let k = rng.gen_range_i32(1, 29);
            let t = (1i32 << k) - 1;
            (t, rng.gen_range_i32(0, 100))
        }
        7 => {
            // odd numbers
            let v = rng.gen_range_i32(1, 1_000_000_000);
            let t = if v % 2 == 0 { v - 1 } else { v };
            let t = if t < 1 { 1 } else { t };
            (t, rng.gen_range_i32(0, 100))
        }
        8 => {
            // small target, large maxDoubles
            (rng.gen_range_i32(1, 20), 100)
        }
        9 => {
            // large target, maxDoubles = 0
            (rng.gen_range_i32(1, 1_000_000_000), 0)
        }
        _ => {
            let t = rng.gen_range_i32(1, 1_000_000_000);
            let m = rng.gen_range_i32(0, 100);
            (t, m)
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
        let (target, max_doubles) = pick_for_mode(&mut rng, mode);
        let target = if target < 1 { 1 } else if target > 1_000_000_000 { 1_000_000_000 } else { target };
        let max_doubles = if max_doubles < 0 { 0 } else if max_doubles > 100 { 100 } else { max_doubles };
        let (t_out, m_out) = generate_test_case(target, max_doubles);
        println!("{{\"target\":{},\"max_doubles\":{}}}", t_out, m_out);
    }
}