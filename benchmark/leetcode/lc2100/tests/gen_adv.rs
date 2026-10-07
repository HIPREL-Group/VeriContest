use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    time_val: i32,
    values: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        0 <= time_val <= 100_000,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    let mut security: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            security.len() == i,
            values.len() == n,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100_000,
            forall |k: int| 0 <= k < security.len() ==> 0 <= #[trigger] security[k] <= 100_000,
            forall |k: int| 0 <= k < security.len() ==> security[k] == values[k],
        decreases n - i,
    {
        security.push(values[i]);
        i = i + 1;
    }
    (security, time_val)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, i32) {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let time_val: i32;
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(0, 100_000);
            for _ in 0..n { v.push(x); }
            time_val = rng.gen_range_i32(0, (n as i32).min(100_000));
        }
        1 => {
            // strictly increasing
            for i in 0..n { v.push((i as i32) % 100_001); }
            time_val = rng.gen_range_i32(0, (n as i32).min(100_000));
        }
        2 => {
            // strictly decreasing
            for i in 0..n {
                let val = (n - 1 - i) as i32 % 100_001;
                v.push(val);
            }
            time_val = rng.gen_range_i32(0, (n as i32).min(100_000));
        }
        3 => {
            // V-shape: decrease then increase
            let mid = n / 2;
            for i in 0..n {
                let d = if i <= mid { (mid - i) as i32 } else { (i - mid) as i32 };
                v.push(d.min(100_000));
            }
            time_val = rng.gen_range_i32(0, ((n/2) as i32).max(1).min(100_000));
        }
        4 => {
            // Mountain
            let mid = n / 2;
            for i in 0..n {
                let d = if i <= mid { i as i32 } else { (n - 1 - i) as i32 };
                v.push(d.min(100_000));
            }
            time_val = rng.gen_range_i32(0, ((n/2) as i32).max(1).min(100_000));
        }
        5 => {
            // random
            for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); }
            time_val = rng.gen_range_i32(0, 100_000);
        }
        6 => {
            // small values random
            for _ in 0..n { v.push(rng.gen_range_i32(0, 3)); }
            time_val = rng.gen_range_i32(0, (n as i32).min(10));
        }
        7 => {
            // time = 0
            for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); }
            time_val = 0;
        }
        8 => {
            // very large time
            for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); }
            time_val = 100_000;
        }
        9 => {
            // plateau with dips
            for i in 0..n {
                if i % 7 == 0 { v.push(50); } else { v.push(100); }
            }
            time_val = rng.gen_range_i32(0, 5);
        }
        _ => {
            // zeros
            for _ in 0..n { v.push(0); }
            time_val = rng.gen_range_i32(0, (n as i32).min(100_000));
        }
    }
    (v, time_val)
}

fn print_json(security: &[i32], time_val: i32) {
    print!("{{\"security\":[");
    for i in 0..security.len() {
        if i > 0 { print!(","); }
        print!("{}", security[i]);
    }
    println!("],\"time\":{}}}", time_val);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 50),
            1 => rng.gen_range_usize(3, 100),
            2 => rng.gen_range_usize(3, 100),
            3 => rng.gen_range_usize(3, 200),
            4 => rng.gen_range_usize(3, 200),
            5 => rng.gen_range_usize(1, 500),
            6 => rng.gen_range_usize(5, 50),
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 10),
            9 => rng.gen_range_usize(5, 100),
            _ => 1,
        };
        let (values, time_val) = build_values(&mut rng, mode, n);
        // clamp time_val
        let time_val = if time_val < 0 { 0 } else if time_val > 100_000 { 100_000 } else { time_val };
        let (security, tv) = generate_test_case(n, time_val, &values);
        print_json(&security, tv);
    }
}