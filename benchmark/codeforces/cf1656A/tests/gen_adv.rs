use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i64>) -> (a: Vec<i64>)
    requires
        1 <= vals.len() <= 200_000,
        forall|i: int| 0 <= i < vals.len() ==> #[trigger] (vals[i] as int) >= 1,
    ensures
        1 <= a.len() <= 200_000,
        forall|t: int| 0 <= t < a.len() ==> #[trigger] (a[t] as int) >= 1,
        a.len() == vals.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == vals[i],
{
    let n = vals.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == vals[k],
            forall|k: int| 0 <= k < vals.len() ==> #[trigger] (vals[k] as int) >= 1,
        decreases n - i,
    {
        a.push(vals[i]);
        i = i + 1;
    }
    a
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn build_vals(mode: usize, n: usize, rng: &mut Rng) -> Vec<i64> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 1_000_000_000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(1);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(1_000_000_000);
            }
        }
        3 => {
            for i in 0..n {
                v.push((i as i64) + 1);
            }
        }
        4 => {
            for i in 0..n {
                v.push((n as i64) - (i as i64));
            }
        }
        5 => {
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(1_000_000_000);
                }
            }
        }
        6 => {
            let x = rng.gen_range_i64(1, 1_000_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        7 => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 10));
            }
        }
        8 => {
            for i in 0..n {
                if i == 0 {
                    v.push(1);
                } else if i == n - 1 {
                    v.push(1_000_000_000);
                } else {
                    v.push(rng.gen_range_i64(1, 1_000_000_000));
                }
            }
        }
        9 => {
            let mid = rng.gen_range_i64(1, 1_000_000_000);
            for i in 0..n {
                if i == 0 {
                    v.push(1);
                } else if i == n - 1 {
                    v.push(1_000_000_000);
                } else {
                    v.push(mid);
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

fn print_json(a: &[i64]) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", a[i]);
    }
    println!("]}}");
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
        let n: usize = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => 1,
            2 => rng.gen_range_usize(2, 10),
            3 => rng.gen_range_usize(1, 1000),
            4 => rng.gen_range_usize(1, 1000),
            5 => rng.gen_range_usize(2, 500),
            6 => rng.gen_range_usize(1, 2000),
            7 => rng.gen_range_usize(1, 50),
            8 => if t < 20 { 100_000 } else { rng.gen_range_usize(2, 100) },
            9 => rng.gen_range_usize(3, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let vals = build_vals(mode, n, &mut rng);
        let a = generate_test_case(&vals);
        let slice: Vec<i64> = a.iter().copied().collect();
        print_json(&slice);
    }
}