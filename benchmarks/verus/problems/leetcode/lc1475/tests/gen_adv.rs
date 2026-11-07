use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (prices: Vec<i32>)
    requires
        1 <= values.len() <= 500,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= prices.len() <= 500,
        prices.len() == values.len(),
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 1000,
{
    let n = values.len();
    let mut prices: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == values.len(),
            1 <= n <= 500,
            0 <= idx <= n,
            prices.len() == idx,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
            forall|i: int| 0 <= i < prices.len() ==> prices[i] == values[i],
            forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 1000,
        decreases n - idx,
    {
        prices.push(values[idx]);
        idx = idx + 1;
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Small random
            let n = rng.gen_range_usize(1, 10);
            (0..n).map(|_| rng.gen_range_i32(1, 1000)).collect()
        }
        1 => {
            // Max length random
            let n = 500;
            (0..n).map(|_| rng.gen_range_i32(1, 1000)).collect()
        }
        2 => {
            // Strictly increasing (no discount for any)
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(1, 1000 - n as i32);
            (0..n).map(|i| start + i as i32).collect()
        }
        3 => {
            // Strictly decreasing (each gets discount from next)
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(n as i32, 1000);
            (0..n).map(|i| start - i as i32).collect()
        }
        4 => {
            // All equal
            let n = rng.gen_range_usize(1, 500);
            let v = rng.gen_range_i32(1, 1000);
            vec![v; n]
        }
        5 => {
            // Single element
            vec![rng.gen_range_i32(1, 1000)]
        }
        6 => {
            // All 1s
            let n = rng.gen_range_usize(1, 500);
            vec![1; n]
        }
        7 => {
            // All 1000s
            let n = rng.gen_range_usize(1, 500);
            vec![1000; n]
        }
        8 => {
            // Alternating high/low
            let n = rng.gen_range_usize(1, 500);
            (0..n).map(|i| if i % 2 == 0 { 1000 } else { 1 }).collect()
        }
        9 => {
            // V-shape
            let n = rng.gen_range_usize(2, 500);
            let mid = n / 2;
            (0..n).map(|i| {
                let d = if i < mid { mid - i } else { i - mid };
                (d as i32 + 1).min(1000)
            }).collect()
        }
        10 => {
            // Example 1
            vec![8, 4, 6, 2, 3]
        }
        11 => {
            // Example 3
            vec![10, 1, 1, 6]
        }
        _ => {
            // Random with many duplicates
            let n = rng.gen_range_usize(1, 500);
            (0..n).map(|_| rng.gen_range_i32(1, 5)).collect()
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
    let modes = 13usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode);
        // Validate in case of bugs
        let mut ok = !values.is_empty() && values.len() <= 500;
        for &v in &values {
            if v < 1 || v > 1000 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let prices = generate_test_case(&values);
        print_json(&prices);
    }
}