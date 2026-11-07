use vstd::prelude::*;

verus! {

pub open spec fn seq_sum(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
    }
}

pub fn generate_test_case(
    rolls: Vec<i32>,
    mean: i32,
    n: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= rolls.len() <= 100_000,
        1 <= n <= 100_000,
        1 <= mean <= 6,
        forall |i: int| 0 <= i < rolls.len() ==> 1 <= #[trigger] rolls[i] <= 6,
    ensures
        1 <= res.0.len() <= 100_000,
        1 <= res.2 <= 100_000,
        1 <= res.1 <= 6,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 6,
{
    (rolls, mean, n)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_rolls(rng: &mut Rng, m: usize, fixed: Option<i32>) -> Vec<i32> {
    let mut v = Vec::with_capacity(m);
    for _ in 0..m {
        let x = match fixed {
            Some(f) => f,
            None => rng.gen_range_i32(1, 6),
        };
        v.push(x);
    }
    v
}

fn print_json(rolls: &[i32], mean: i32, n: i32) {
    print!("{{\"rolls\":[");
    for i in 0..rolls.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", rolls[i]);
    }
    println!("],\"mean\":{},\"n\":{}}}", mean, n);
}

fn make_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // Small random case
            let m = rng.gen_range_usize(1, 10);
            let n = rng.gen_range_usize(1, 10) as i32;
            let mean = rng.gen_range_i32(1, 6);
            (build_rolls(rng, m, None), mean, n)
        }
        1 => {
            // Mean = 1, all rolls = 1 (boundary: sum must be exactly n)
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(1, 100) as i32;
            (build_rolls(rng, m, Some(1)), 1, n)
        }
        2 => {
            // Mean = 6, all rolls = 6 (boundary: sum must be exactly 6n)
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(1, 100) as i32;
            (build_rolls(rng, m, Some(6)), 6, n)
        }
        3 => {
            // Mean = 6 but rolls are 1 (likely infeasible)
            let m = rng.gen_range_usize(1, 50);
            let n = rng.gen_range_usize(1, 50) as i32;
            (build_rolls(rng, m, Some(1)), 6, n)
        }
        4 => {
            // Mean = 1 but rolls are 6 (likely infeasible)
            let m = rng.gen_range_usize(1, 50);
            let n = rng.gen_range_usize(1, 50) as i32;
            (build_rolls(rng, m, Some(6)), 1, n)
        }
        5 => {
            // Max sizes
            let m = 100_000usize;
            let n = 100_000i32;
            let mean = rng.gen_range_i32(1, 6);
            (build_rolls(rng, m, None), mean, n)
        }
        6 => {
            // n=1
            let m = rng.gen_range_usize(1, 100);
            let mean = rng.gen_range_i32(1, 6);
            (build_rolls(rng, m, None), mean, 1)
        }
        7 => {
            // m=1
            let n = rng.gen_range_usize(1, 100) as i32;
            let mean = rng.gen_range_i32(1, 6);
            (build_rolls(rng, 1, None), mean, n)
        }
        8 => {
            // Exactly feasible: mean=3, rolls=3
            let m = rng.gen_range_usize(1, 200);
            let n = rng.gen_range_usize(1, 200) as i32;
            (build_rolls(rng, m, Some(3)), 3, n)
        }
        9 => {
            // Mix of extreme rolls
            let m = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(m);
            for i in 0..m {
                v.push(if i % 2 == 0 { 1 } else { 6 });
            }
            let n = rng.gen_range_usize(1, 200) as i32;
            let mean = rng.gen_range_i32(1, 6);
            (v, mean, n)
        }
        _ => {
            let m = rng.gen_range_usize(1, 1000);
            let n = rng.gen_range_usize(1, 1000) as i32;
            let mean = rng.gen_range_i32(1, 6);
            let _ = t;
            (build_rolls(rng, m, None), mean, n)
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
        let (rolls, mean, n) = make_case(&mut rng, mode, t);
        let (rolls2, mean2, n2) = generate_test_case(rolls, mean, n);
        print_json(&rolls2, mean2, n2);
    }
}