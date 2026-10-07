use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 1000,
    ensures
        1 <= result <= 1000,
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

fn pick_n_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 1000,
        2 => 2,
        3 => 3,
        4 => 5,
        5 => 7,
        6 => 999,
        7 => 105, // lcm(3,5,7)
        8 => rng.gen_range_i32(1, 20),
        9 => rng.gen_range_i32(100, 200),
        _ => {
            let seeds = [21, 35, 15, 104, 106, 210, 500, 750, 333, 555, 777];
            seeds[t % seeds.len()]
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let mut n = pick_n_for_mode(&mut rng, mode, t);
        if n < 1 { n = 1; }
        if n > 1000 { n = 1000; }
        let result = generate_test_case(n);
        println!("{{\"n\":{}}}", result);
    }
}