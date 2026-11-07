use vstd::prelude::*;

verus! {

pub fn generate_test_case(num1: i32, num2: i32, num3: i32) -> (result: (i32, i32, i32))
    requires
        1 <= num1 <= 9999,
        1 <= num2 <= 9999,
        1 <= num3 <= 9999,
    ensures
        1 <= result.0 <= 9999,
        1 <= result.1 <= 9999,
        1 <= result.2 <= 9999,
{
    (num1, num2, num3)
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (rng.gen_range_i32(1, 9), rng.gen_range_i32(1, 9), rng.gen_range_i32(1, 9)),
        1 => (1, 1, 1),
        2 => (9999, 9999, 9999),
        3 => (1, 10, 1000),
        4 => (987, 879, 798),
        5 => (1, 2, 3),
        6 => (rng.gen_range_i32(1, 9999), 1, 9999),
        7 => (rng.gen_range_i32(10, 99), rng.gen_range_i32(100, 999), rng.gen_range_i32(1000, 9999)),
        8 => {
            let d = rng.gen_range_i32(0, 9).max(1);
            let n = d * 1111;
            (n, n, n)
        }
        9 => (rng.gen_range_i32(1000, 9999), rng.gen_range_i32(1000, 9999), rng.gen_range_i32(1000, 9999)),
        _ => (rng.gen_range_i32(1, 9999), rng.gen_range_i32(1, 9999), rng.gen_range_i32(1, 9999)),
    }
}

fn clamp(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 9999 { 9999 } else { v }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (a, b, c) = pick_for_mode(&mut rng, mode);
        let (n1, n2, n3) = generate_test_case(clamp(a), clamp(b), clamp(c));
        println!("{{\"num1\":{},\"num2\":{},\"num3\":{}}}", n1, n2, n3);
    }
}