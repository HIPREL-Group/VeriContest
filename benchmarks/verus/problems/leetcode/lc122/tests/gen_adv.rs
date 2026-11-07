use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (prices: Vec<i32>)
    requires
        1 <= values.len() <= 30_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= prices.len() <= 30_000,
        forall|i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10_000,
{
    let n = values.len();
    let mut prices: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            prices.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] prices[k] <= 10_000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 10_000,
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(0, 10_000)]
        }
        1 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            let mut cur = rng.gen_range_i32(0, 50);
            for _ in 0..n {
                v.push(cur);
                let inc = rng.gen_range_i32(1, 50);
                if cur + inc <= 10_000 {
                    cur += inc;
                } else {
                    cur = 10_000;
                }
            }
            v
        }
        2 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            let mut cur = rng.gen_range_i32(5_000, 10_000);
            for _ in 0..n {
                v.push(cur);
                let dec = rng.gen_range_i32(1, 50);
                if cur - dec >= 0 {
                    cur -= dec;
                } else {
                    cur = 0;
                }
            }
            v
        }
        3 => {
            // all same
            let n = rng.gen_range_usize(1, 200);
            let val = rng.gen_range_i32(0, 10_000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(val);
            }
            v
        }
        4 => {
            // all zeros
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(0);
            }
            v
        }
        5 => {
            // extremes 0 and 10000 alternating
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(10_000);
                }
            }
            v
        }
        6 => {
            // maximum length random
            let n = 30_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            v
        }
        7 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            v
        }
        8 => {
            // zigzag (big swings)
            let n = rng.gen_range_usize(2, 300);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(0, 1_000));
                } else {
                    v.push(rng.gen_range_i32(9_000, 10_000));
                }
            }
            v
        }
        9 => {
            // two elements edge cases
            let a = rng.gen_range_i32(0, 10_000);
            let b = rng.gen_range_i32(0, 10_000);
            vec![a, b]
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(100, 1_000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
            v
        }
    }
}

fn print_json(prices: &[i32]) {
    print!("{{\"prices\":[");
    for i in 0..prices.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", prices[i]);
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        let prices = generate_test_case(&values);
        print_json(&prices);
    }
}