use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 19,
    ensures
        1 <= result <= 19,
{
    n
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_n_for_mode(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 19,
        4 => 18,
        5 => rng.gen_range_i32(1, 19),
        6 => rng.gen_range_i32(10, 19),
        7 => rng.gen_range_i32(1, 5),
        8 => rng.gen_range_i32(5, 15),
        9 => 10,
        _ => rng.gen_range_i32(1, 19),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_n_for_mode(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 19 { 19 } else { n };
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}