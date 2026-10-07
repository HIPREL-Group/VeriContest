use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    prices: Vec<i32>,
    fee: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= prices.len() <= 50_000,
        forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] < 50_000,
        0 <= fee < 50_000,
    ensures
        1 <= res.0.len() <= 50_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] < 50_000,
        0 <= res.1 < 50_000,
{
    (prices, fee)
}

pub fn build_prices(
    values: &Vec<i32>,
    n: usize,
) -> (res: Vec<i32>)
    requires
        1 <= n <= 50_000,
        values.len() >= n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] < 50_000,
    ensures
        res.len() == n,
        forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] < 50_000,
{
    let mut out: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            out.len() == k,
            values.len() >= n,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] < 50_000,
            forall |i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] < 50_000,
        decreases n - k,
    {
        out.push(values[k]);
        k = k + 1;
    }
    out
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 49_999)); }
        }
        1 => {
            let c = rng.gen_range_i32(1, 49_999);
            for _ in 0..n { v.push(c); }
        }
        2 => {
            for i in 0..n {
                let x = 1 + (i as i32 % 49_999);
                v.push(x);
            }
        }
        3 => {
            for i in 0..n {
                let x = 49_999 - (i as i32 % 49_999);
                let x = if x < 1 { 1 } else { x };
                v.push(x);
            }
        }
        4 => {
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(49_999); }
            }
        }
        5 => {
            for _ in 0..n { v.push(1); }
        }
        6 => {
            for _ in 0..n { v.push(49_999); }
        }
        7 => {
            // small range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
        }
        8 => {
            // sawtooth
            for i in 0..n {
                let x = 1 + ((i as i32 * 7) % 100);
                v.push(x);
            }
        }
        9 => {
            // big then small
            for i in 0..n {
                if i < n / 2 { v.push(rng.gen_range_i32(40_000, 49_999)); }
                else { v.push(rng.gen_range_i32(1, 100)); }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 49_999)); }
        }
    }
    v
}

fn print_json(prices: &[i32], fee: i32) {
    print!("{{\"prices\":[");
    for i in 0..prices.len() {
        if i > 0 { print!(","); }
        print!("{}", prices[i]);
    }
    println!("],\"fee\":{}}}", fee);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => rng.gen_range_usize(1, 50),
            2 => 1,
            3 => 2,
            4 => rng.gen_range_usize(10, 200),
            5 => rng.gen_range_usize(1, 1000),
            6 => rng.gen_range_usize(1, 500),
            7 => rng.gen_range_usize(1, 50),
            8 => if t % 2 == 0 { 50_000 } else { rng.gen_range_usize(100, 1000) },
            9 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let fee: i32 = match mode {
            2 => 0,
            3 => 49_999,
            5 => rng.gen_range_i32(0, 10),
            6 => rng.gen_range_i32(40_000, 49_999),
            _ => rng.gen_range_i32(0, 49_999),
        };

        let values = make_values(&mut rng, n, mode);
        let prices = build_prices(&values, n);
        let (p, f) = generate_test_case(prices, fee);
        print_json(&p, f);
    }
}