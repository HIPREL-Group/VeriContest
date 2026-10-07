use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        1 <= n <= 50,
    ensures
        1 <= result <= 50,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => 9,
        3 => 10,
        4 => 11,
        5 => 12,
        6 => 50,
        7 => 49,
        8 => ((t % 50) + 1) as i32,
        9 => {
            // boundary clustering around 10
            let cands = [9, 10, 11, 12, 13, 14, 15];
            cands[t % cands.len()] as i32
        }
        _ => rng.gen_range_i32(1, 50),
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
        let n = pick_for_mode(&mut rng, mode, t);
        let n = if n < 1 { 1 } else if n > 50 { 50 } else { n };
        let result = generate_test_case(n);
        println!("{{\"n\": {}}}", result);
    }
}