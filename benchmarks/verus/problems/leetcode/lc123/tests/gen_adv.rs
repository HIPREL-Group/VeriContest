use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (prices: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= prices.len() <= 100_000,
        forall |i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 100_000,
{
    let n = values.len();
    let mut prices: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            prices.len() == i,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] prices[k] <= 100_000,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100_000,
            forall |k: int| 0 <= k < i as int ==> prices[k] == values[k],
        decreases n - i,
    {
        prices.push(values[i]);
        i = i + 1;
    }
    prices
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    v.into_iter().map(|x| if x < 0 { 0 } else if x > 100_000 { 100_000 } else { x }).collect()
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element
            let n = rng.range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(0, 100_000)); }
            v
        }
        1 => {
            // Strictly increasing
            let n = rng.range_usize(2, 200);
            let mut v = Vec::new();
            let mut cur = 0;
            for _ in 0..n {
                cur += rng.range_i32(0, 100) as i32;
                if cur > 100_000 { cur = 100_000; }
                v.push(cur);
            }
            v
        }
        2 => {
            // Strictly decreasing
            let n = rng.range_usize(2, 200);
            let mut v = Vec::new();
            let mut cur: i32 = 100_000;
            for _ in 0..n {
                v.push(cur);
                cur -= rng.range_i32(0, 100) as i32;
                if cur < 0 { cur = 0; }
            }
            v
        }
        3 => {
            // All same
            let n = rng.range_usize(1, 200);
            let val = rng.range_i32(0, 100_000);
            vec![val; n]
        }
        4 => {
            // Two peaks (classic two-transaction case)
            let n = rng.range_usize(6, 100);
            let mut v = Vec::new();
            let quarter = n / 4;
            for i in 0..n {
                let segment = i / (quarter.max(1));
                let val = match segment {
                    0 => (i * 100) as i32,
                    1 => 100_000 - (i * 100) as i32,
                    2 => (i * 200) as i32,
                    _ => 100_000 - (i * 50) as i32,
                };
                v.push(val);
            }
            clamp_vec(v)
        }
        5 => {
            // Random small range
            let n = rng.range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(0, 10)); }
            v
        }
        6 => {
            // Random full range
            let n = rng.range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(0, 100_000)); }
            v
        }
        7 => {
            // Zeros
            let n = rng.range_usize(1, 100);
            vec![0; n]
        }
        8 => {
            // Max size
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.range_i32(0, 100_000)); }
            v
        }
        9 => {
            // V shape
            let n = rng.range_usize(3, 100);
            let mid = n / 2;
            let mut v = Vec::new();
            for i in 0..n {
                let d = if i <= mid { mid - i } else { i - mid };
                v.push((d * 1000) as i32);
            }
            clamp_vec(v)
        }
        10 => {
            // Known example
            vec![3,3,5,0,0,3,1,4]
        }
        11 => {
            // Example 2
            vec![1,2,3,4,5]
        }
        12 => {
            // Example 3
            vec![7,6,4,3,1]
        }
        _ => {
            // Alternating
            let n = rng.range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 100_000 });
            }
            v
        }
    }
}

fn print_json(prices: &[i32]) {
    print!("{{\"prices\":[");
    for i in 0..prices.len() {
        if i > 0 { print!(","); }
        print!("{}", prices[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 14usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = gen_mode(&mut rng, mode);
        let clamped = clamp_vec(raw);
        let values = if clamped.is_empty() { vec![0] } else if clamped.len() > 100_000 { clamped[..100_000].to_vec() } else { clamped };
        let prices = generate_test_case(&values);
        print_json(&prices);
    }
}