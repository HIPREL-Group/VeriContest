use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, m_val: i32) -> (result: (i32, i32))
    requires
        1 <= n_val <= 1000,
        1 <= m_val <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
{
    (n_val, m_val)
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (1000, 1000),
        2 => (1, 1000),
        3 => (1000, 1),
        4 => (rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        5 => {
            let n = rng.gen_range_i32(1, 1000);
            (n, n)
        }
        6 => {
            let m = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_i32(1, 1000 / m.max(1));
            (m * k, m)
        }
        7 => (rng.gen_range_i32(1, 1000), 1),
        8 => (rng.gen_range_i32(1, 1000), 1000),
        9 => {
            let m = rng.gen_range_i32(500, 1000);
            let n = rng.gen_range_i32(1, m - 1);
            (n, m)
        }
        _ => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
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
        let (n, m) = pick_for_mode(&mut rng, mode);
        let n_clamped = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let m_clamped = if m < 1 { 1 } else if m > 1000 { 1000 } else { m };
        let (nn, mm) = generate_test_case(n_clamped, m_clamped);
        println!("{{\"n\": {}, \"m\": {}}}", nn, mm);
    }
}