use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    values: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 200000,
        1 <= k_val as int <= n as int,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000000,
    ensures
        1 <= result.0.len() <= 200000,
        1 <= result.1 as int <= result.0.len() as int,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100000000,
{
    let mut happiness: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            happiness.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] happiness[j] <= 100000000,
            forall |j: int| 0 <= j < i as int ==> happiness[j] == values[j],
            forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 100000000,
        decreases n - i,
    {
        happiness.push(values[i]);
        i += 1;
    }
    (happiness, k_val)
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_i32(1, 100)); }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(100_000_000); }
        }
        3 => {
            for i in 0..n { v.push((i as i32 % 100_000_000) + 1); }
        }
        4 => {
            for i in 0..n { v.push((n as i32 - i as i32).max(1)); }
        }
        5 => {
            for _ in 0..n { v.push(rng.gen_i32(1, 100_000_000)); }
        }
        6 => {
            let c = rng.gen_i32(1, 100_000_000);
            for _ in 0..n { v.push(c); }
        }
        7 => {
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100_000_000); }
            }
        }
        8 => {
            for _ in 0..n { v.push(rng.gen_i32(1, 10)); }
        }
        9 => {
            let base = rng.gen_i32(1, 100_000_000 - n as i32 - 1).max(1);
            for i in 0..n {
                let val = base + i as i32;
                v.push(val.min(100_000_000).max(1));
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_i32(1, 1000)); }
        }
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_usize(1, 20),
            1 => 1,
            2 => 200_000,
            3 => rng.gen_usize(1, 100),
            4 => rng.gen_usize(2, 50),
            5 => rng.gen_usize(1, 5000),
            6 => rng.gen_usize(1, 1000),
            7 => 2,
            8 => rng.gen_usize(10, 100),
            9 => rng.gen_usize(1, 1000),
            _ => rng.gen_usize(1, 500),
        };

        let values = build_values(&mut rng, mode, n);
        let k = match mode {
            1 => 1,
            2 => rng.gen_usize(1, n) as i32,
            3 => 1,
            4 => n as i32,
            _ => rng.gen_usize(1, n) as i32,
        };

        let (happiness, k_out) = generate_test_case(n, k, &values);

        print!("{{\"happiness\":[");
        for i in 0..happiness.len() {
            if i > 0 { print!(","); }
            print!("{}", happiness[i]);
        }
        println!("],\"k\":{}}}", k_out);
    }
}