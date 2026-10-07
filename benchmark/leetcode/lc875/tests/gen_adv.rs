use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    piles: Vec<i32>,
    h: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= piles.len() <= 10_000,
        forall |i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 1_000_000_000,
        piles.len() <= h <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 10_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        result.0.len() <= result.1 <= 1_000_000_000,
{
    (piles, h)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 100));
            }
            let h = rng.gen_range_i32(n as i32, (n as i32) + 20);
            (piles, h)
        }
        1 => {
            // h == n (minimum)
            let n = rng.gen_range_usize(1, 100);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (piles, n as i32)
        }
        2 => {
            // h huge
            let n = rng.gen_range_usize(1, 100);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (piles, 1_000_000_000)
        }
        3 => {
            // single pile
            let piles = vec![rng.gen_range_i32(1, 1_000_000_000)];
            let h = rng.gen_range_i32(1, 1_000_000_000);
            (piles, h)
        }
        4 => {
            // all max piles
            let n = rng.gen_range_usize(1, 1000);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(1_000_000_000);
            }
            let h = rng.gen_range_i32(n as i32, 1_000_000_000);
            (piles, h)
        }
        5 => {
            // all 1s
            let n = rng.gen_range_usize(1, 1000);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(1);
            }
            let h = rng.gen_range_i32(n as i32, (n as i32) * 2);
            (piles, h)
        }
        6 => {
            // examples from problem
            match t % 3 {
                0 => (vec![3, 6, 7, 11], 8),
                1 => (vec![30, 11, 23, 4, 20], 5),
                _ => (vec![30, 11, 23, 4, 20], 6),
            }
        }
        7 => {
            // max length
            let n = 10_000usize;
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            let h = rng.gen_range_i32(n as i32, 1_000_000_000);
            (piles, h)
        }
        8 => {
            // one huge pile, many small
            let n = rng.gen_range_usize(2, 500);
            let mut piles = Vec::new();
            piles.push(1_000_000_000);
            for _ in 1..n {
                piles.push(rng.gen_range_i32(1, 10));
            }
            let h = rng.gen_range_i32(n as i32, 1_000_000_000);
            (piles, h)
        }
        9 => {
            // h = n + something small (tight)
            let n = rng.gen_range_usize(1, 100);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            let extra = rng.gen_range_i32(0, 5);
            let h = (n as i32).saturating_add(extra).min(1_000_000_000);
            (piles, h)
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(1, 500);
            let mut piles = Vec::new();
            for _ in 0..n {
                piles.push(rng.gen_range_i32(1, 1_000_000));
            }
            let h = rng.gen_range_i32(n as i32, 1_000_000_000);
            (piles, h)
        }
    }
}

fn print_json(piles: &[i32], h: i32) {
    print!("{{\"piles\":[");
    for i in 0..piles.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", piles[i]);
    }
    println!("],\"h\":{}}}", h);
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
        let (piles, h) = build(&mut rng, mode, t);
        let (p, hh) = generate_test_case(piles, h);
        print_json(&p, hh);
    }
}