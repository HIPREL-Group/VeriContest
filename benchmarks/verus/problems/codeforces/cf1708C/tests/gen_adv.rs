use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    q_val: i64,
    values: &Vec<i64>,
) -> (result: (Vec<i64>, i64))
    requires
        1 <= n <= 100_000,
        1 <= q_val <= 1_000_000_000,
        values.len() == n,
        forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000,
        forall |j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1_000_000_000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            values.len() == n,
            forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
    (a, q_val)
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn build_values(rng: &mut Rng, n: usize, mode: usize, q: i64) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 10));
            }
        }
        1 => {
            // all 1
            for _ in 0..n {
                v.push(1);
            }
        }
        2 => {
            // all huge
            for _ in 0..n {
                v.push(1_000_000_000);
            }
        }
        3 => {
            // strictly increasing
            let start = rng.gen_range_i64(1, 100);
            for i in 0..n {
                v.push(start + i as i64);
            }
        }
        4 => {
            // strictly decreasing
            for i in 0..n {
                let val = (n as i64 - i as i64).max(1);
                v.push(val);
            }
        }
        5 => {
            // equal to q
            for _ in 0..n {
                v.push(q);
            }
        }
        6 => {
            // half below, half above q
            for i in 0..n {
                if i % 2 == 0 {
                    v.push((q - 1).max(1));
                } else {
                    v.push((q + 1).min(1_000_000_000));
                }
            }
        }
        7 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 1_000_000_000));
            }
        }
        8 => {
            // all larger than q
            for _ in 0..n {
                v.push((q + 1).min(1_000_000_000));
            }
        }
        9 => {
            // alternating 1 and big
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(1_000_000_000);
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 1_000_000_000));
            }
        }
    }
    v
}

fn print_json(a: &[i64], q: i64) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    println!("],\"q\":{}}}", q);
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
            0 => rng.gen_range_usize(1, 20),
            1 => 100_000,
            2 => 100_000,
            3 => rng.gen_range_usize(1, 100),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(1, 1000),
            6 => rng.gen_range_usize(1, 1000),
            7 => rng.gen_range_usize(1, 5000),
            8 => rng.gen_range_usize(1, 500),
            9 => rng.gen_range_usize(1, 500),
            _ => rng.gen_range_usize(1, 1000),
        };
        let n = n.max(1).min(100_000);

        let q = match mode {
            1 => 1,
            2 => 1_000_000_000,
            5 => rng.gen_range_i64(1, 1_000_000_000),
            6 => rng.gen_range_i64(2, 1_000_000_000 - 1),
            8 => rng.gen_range_i64(1, 500_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000),
        };

        let values = build_values(&mut rng, n, mode, q);
        let (a, q_out) = generate_test_case(n, q, &values);
        print_json(&a, q_out);
    }
}