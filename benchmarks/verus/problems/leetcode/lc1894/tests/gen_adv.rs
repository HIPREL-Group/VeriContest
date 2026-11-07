use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    chalk_vals: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= chalk_vals.len() <= 100_000,
        forall |i: int| 0 <= i < chalk_vals.len() ==> 1 <= #[trigger] chalk_vals[i] <= 100_000,
        1 <= k <= 1_000_000_000,
    ensures
        1 <= res.0.len() <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100_000,
        1 <= res.1 <= 1_000_000_000,
{
    let n = chalk_vals.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == chalk_vals.len(),
            0 <= i <= n,
            out.len() == i,
            forall |j: int| 0 <= j < i ==> 1 <= #[trigger] out[j] <= 100_000,
            forall |j: int| 0 <= j < chalk_vals.len() ==> 1 <= #[trigger] chalk_vals[j] <= 100_000,
        decreases n - i,
    {
        let v = chalk_vals[i];
        assert(1 <= v <= 100_000);
        out.push(v);
        i = i + 1;
    }
    (out, k)
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
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_chalk(rng: &mut Rng, n: usize, min_v: i32, max_v: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(min_v, max_v));
    }
    v
}

fn print_json(chalk: &[i32], k: i32) {
    print!("{{\"chalk\":[");
    for i in 0..chalk.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", chalk[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn pick_k(rng: &mut Rng, chalk: &[i32], mode: usize) -> i32 {
    // sum of chalk, capped
    let mut sum: i64 = 0;
    for &x in chalk {
        sum += x as i64;
    }
    let cap: i64 = 1_000_000_000;
    match mode {
        0 => 1,
        1 => cap as i32,
        2 => {
            // k less than first chalk
            if chalk.is_empty() { 1 } else {
                let c0 = chalk[0];
                if c0 <= 1 { 1 } else { rng.gen_range_i32(0, c0 - 1).max(1) }
            }
        }
        3 => {
            // k exactly equal to sum - 1
            let s = sum.min(cap);
            (s - 1).max(1).min(cap) as i32
        }
        4 => {
            // k equal to sum (will trigger wrap)
            let s = sum.min(cap);
            s.max(1) as i32
        }
        5 => {
            // k just above sum
            let s = (sum + 1).min(cap);
            s.max(1) as i32
        }
        6 => {
            // Very large k
            rng.gen_range_i32(900_000_000, 1_000_000_000)
        }
        7 => {
            // Medium k
            rng.gen_range_i32(1, (cap.min(sum * 3) as i32).max(1))
        }
        8 => {
            // k = sum - chalk[0] (will replace at student 0 on second round)
            let s = sum.min(cap);
            let target = (s - chalk[0] as i64).max(1).min(cap);
            target as i32
        }
        9 => {
            // k small
            rng.gen_range_i32(1, 100)
        }
        _ => rng.gen_range_i32(1, 1_000_000_000),
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 2 + (t % 5),
            2 => 10,
            3 => 100,
            4 => 1000,
            5 => 50_000,
            6 => 100_000,
            7 => rng.gen_range_usize(1, 500),
            8 => rng.gen_range_usize(1, 10_000),
            _ => rng.gen_range_usize(1, 100_000),
        };

        // For very large n, use smaller values to avoid excessive time
        let (min_v, max_v) = match mode {
            0 => (1, 100_000),
            1 => (1, 10),
            2 => (1, 100_000),
            3 => (100_000, 100_000),
            4 => (1, 1),
            5 => (1, 100),
            6 => (1, 100_000),
            7 => (1, 100_000),
            8 => (1, 50_000),
            _ => (1, 100_000),
        };

        let chalk = build_chalk(&mut rng, n, min_v, max_v);
        let k = pick_k(&mut rng, &chalk, mode);
        let k = if k < 1 { 1 } else if k > 1_000_000_000 { 1_000_000_000 } else { k };

        let (out_chalk, out_k) = generate_test_case(&chalk, k);
        print_json(&out_chalk, out_k);
    }
}