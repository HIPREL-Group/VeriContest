use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i32>) -> (position: Vec<i32>)
    requires
        1 <= n <= 100,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= position.len() <= 100,
        forall |i: int| 0 <= i < position.len() ==> 1 <= #[trigger] position[i] <= 1_000_000_000,
{
    let mut position: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= k <= n,
            position.len() == k,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < position.len() ==> position[i] == values[i],
            forall |i: int| 0 <= i < position.len() ==> 1 <= #[trigger] position[i] <= 1_000_000_000,
        decreases n - k,
    {
        position.push(values[k]);
        k = k + 1;
    }
    position
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
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
                v.push(if i % 2 == 0 { 1 } else { 2 });
            }
        }
        4 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 2 } else { 3 });
            }
        }
        5 => {
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 1 } else { 2 });
            }
        }
        6 => {
            for i in 0..n {
                v.push((i as i32 % 1_000_000_000) + 1);
            }
        }
        7 => {
            // all odd
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 500_000_000);
                v.push(2 * x - 1);
            }
        }
        8 => {
            // all even
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 500_000_000);
                v.push(2 * x);
            }
        }
        9 => {
            // mostly odd with one even
            for i in 0..n {
                if i == 0 {
                    v.push(2);
                } else {
                    v.push(2 * rng.gen_range_i32(1, 500_000_000) - 1);
                }
            }
        }
        _ => {
            // mostly even with one odd
            for i in 0..n {
                if i == 0 {
                    v.push(1);
                } else {
                    v.push(2 * rng.gen_range_i32(1, 500_000_000));
                }
            }
        }
    }
    v
}

fn print_json(position: &[i32]) {
    print!("{{\"position\":[");
    for i in 0..position.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", position[i]);
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => 1,
            2 => 100,
            3 => 2,
            4 => 3,
            5 => rng.gen_range_usize(1, 50),
            6 => 100,
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 100),
            9 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(2, 100),
        };
        let values = build_values(&mut rng, mode, n);
        let position = generate_test_case(n, &values);
        print_json(&position);
    }
}