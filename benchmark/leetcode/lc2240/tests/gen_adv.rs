use vstd::prelude::*;

verus! {

pub fn generate_test_case(total: i32, cost1: i32, cost2: i32) -> (r: (i32, i32, i32))
    requires
        1 <= total <= 1000000,
        1 <= cost1 <= 1000000,
        1 <= cost2 <= 1000000,
    ensures
        1 <= r.0 <= 1000000,
        1 <= r.1 <= 1000000,
        1 <= r.2 <= 1000000,
{
    (total, cost1, cost2)
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (rng.gen_range_i32(1, 1000000), rng.gen_range_i32(1, 1000000), rng.gen_range_i32(1, 1000000)),
        1 => (1, 1, 1),
        2 => (1000000, 1000000, 1000000),
        3 => (1000000, 1, 1),
        4 => (1, 1000000, 1000000),
        5 => (1000000, 1, 1000000),
        6 => (1000000, 1000000, 1),
        7 => (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
        8 => {
            let t = rng.gen_range_i32(1, 1000000);
            let c1 = rng.gen_range_i32(t + 1 - (if t >= 1000000 { 1 } else { 0 }), 1000000).max(1);
            let c2 = rng.gen_range_i32(t + 1 - (if t >= 1000000 { 1 } else { 0 }), 1000000).max(1);
            (t, c1, c2)
        }
        9 => {
            let t = rng.gen_range_i32(1, 1000000);
            (t, 1, 1)
        }
        10 => {
            // total exactly divisible
            let c1 = rng.gen_range_i32(1, 1000);
            let c2 = rng.gen_range_i32(1, 1000);
            let mult = rng.gen_range_i32(1, 1000);
            let t = (c1 * mult).min(1000000).max(1);
            (t, c1, c2)
        }
        _ => (20, 10, 5),
    }
}

fn print_json(total: i32, cost1: i32, cost2: i32) {
    println!("{{\"total\":{},\"cost1\":{},\"cost2\":{}}}", total, cost1, cost2);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total_cases = 220usize;

    for t in 0..total_cases {
        let mode = t % modes;
        let (total, c1, c2) = pick_for_mode(&mut rng, mode);
        let total = total.max(1).min(1000000);
        let c1 = c1.max(1).min(1000000);
        let c2 = c2.max(1).min(1000000);
        let r = generate_test_case(total, c1, c2);
        print_json(r.0, r.1, r.2);
    }
}