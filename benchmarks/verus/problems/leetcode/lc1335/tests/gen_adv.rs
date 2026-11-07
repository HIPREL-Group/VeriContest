use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    jobs: Vec<i32>,
    d: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= jobs.len() <= 300,
        forall|i: int| 0 <= i < jobs.len() ==> 0 <= #[trigger] jobs[i] <= 1000,
        1 <= d <= 10,
    ensures
        1 <= result.0.len() <= 300,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 10,
{
    (jobs, d)
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
        self.state = self
            .state
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Tiny: n=1
            let v = rng.gen_range_i32(0, 1000);
            (vec![v], 1)
        }
        1 => {
            // d > n (should return -1)
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            let d = rng.gen_range_i32(n as i32 + 1, 10);
            (v, d)
        }
        2 => {
            // d == n
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            (v, n as i32)
        }
        3 => {
            // d == 1
            let n = rng.gen_range_usize(1, 300);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            (v, 1)
        }
        4 => {
            // Decreasing (like example 1)
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            let mut x = rng.gen_range_i32(500, 1000);
            for _ in 0..n {
                v.push(x);
                if x > 0 {
                    x -= 1;
                }
            }
            let d = rng.gen_range_i32(1, n.min(10) as i32);
            (v, d)
        }
        5 => {
            // Increasing
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            let mut x: i32 = 0;
            for _ in 0..n {
                v.push(x);
                if x < 1000 {
                    x += rng.gen_range_i32(0, 20);
                    if x > 1000 { x = 1000; }
                }
            }
            let d = rng.gen_range_i32(1, n.min(10) as i32);
            (v, d)
        }
        6 => {
            // All zeros
            let n = rng.gen_range_usize(1, 300);
            let v = vec![0i32; n];
            let d = rng.gen_range_i32(1, n.min(10) as i32);
            (v, d)
        }
        7 => {
            // All same (non-zero)
            let n = rng.gen_range_usize(1, 300);
            let c = rng.gen_range_i32(1, 1000);
            let v = vec![c; n];
            let d = rng.gen_range_i32(1, n.min(10) as i32);
            (v, d)
        }
        8 => {
            // Max length
            let n = 300usize;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            let d = rng.gen_range_i32(1, 10);
            (v, d)
        }
        9 => {
            // Single big peak
            let n = rng.gen_range_usize(5, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            let peak = rng.gen_range_usize(0, n - 1);
            v[peak] = 1000;
            let d = rng.gen_range_i32(1, n.min(10) as i32);
            (v, d)
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 300);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            let dmax = n.min(10) as i32;
            let d = if t % 3 == 0 {
                rng.gen_range_i32(1, 10)
            } else {
                rng.gen_range_i32(1, dmax)
            };
            (v, d)
        }
    }
}

fn print_json(jobs: &[i32], d: i32) {
    print!("{{\"job_difficulty\":[");
    for i in 0..jobs.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", jobs[i]);
    }
    println!("],\"d\":{}}}", d);
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
        let (jobs, d) = build(&mut rng, mode, t);
        // Sanity-clamp
        if jobs.is_empty() || jobs.len() > 300 {
            continue;
        }
        if d < 1 || d > 10 {
            continue;
        }
        let mut ok = true;
        for &x in &jobs {
            if x < 0 || x > 1000 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let (j, dd) = generate_test_case(jobs, d);
        print_json(&j, dd);
    }
}