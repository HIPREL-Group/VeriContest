use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: &Vec<i32>,
) -> (prices: Vec<i32>)
    requires
        1 <= raw.len() <= 100_000,
        forall |i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] <= 10_000,
    ensures
        1 <= prices.len() <= 100_000,
        forall |i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10_000,
{
    let n = raw.len();
    let mut prices: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw.len(),
            0 <= i <= n,
            prices.len() == i,
            forall |k: int| 0 <= k < raw.len() ==> 0 <= #[trigger] raw[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] prices[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> prices[k] == raw[k],
        decreases n - i,
    {
        prices.push(raw[i]);
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

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_i32(0, 10_000)]
        }
        1 => {
            // strictly decreasing (profit = 0)
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::new();
            let mut cur = 10_000i32;
            for _ in 0..n {
                v.push(cur);
                if cur > 0 { cur -= 1; }
            }
            v
        }
        2 => {
            // strictly increasing (max profit = last - first)
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::new();
            let mut cur = 0i32;
            for _ in 0..n {
                v.push(cur);
                if cur < 10_000 { cur += 1; }
            }
            v
        }
        3 => {
            // all same
            let n = rng.gen_usize(1, 200);
            let x = rng.gen_i32(0, 10_000);
            vec![x; n]
        }
        4 => {
            // all zeros
            let n = rng.gen_usize(1, 500);
            vec![0i32; n]
        }
        5 => {
            // all max
            let n = rng.gen_usize(1, 500);
            vec![10_000i32; n]
        }
        6 => {
            // random
            let n = rng.gen_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            v
        }
        7 => {
            // valley pattern: min deep in middle
            let n = rng.gen_usize(5, 300);
            let mut v = Vec::new();
            for i in 0..n {
                let mid = n / 2;
                let d = if i > mid { i - mid } else { mid - i };
                v.push((d as i32).min(10_000));
            }
            v
        }
        8 => {
            // classic: [7,1,5,3,6,4]
            vec![7,1,5,3,6,4]
        }
        9 => {
            // large: 100_000 random elements
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            v
        }
        10 => {
            // min at end, max at start (no profit)
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::new();
            v.push(10_000);
            for _ in 1..n { v.push(rng.gen_i32(0, 9_999)); }
            v
        }
        11 => {
            // min at start, max at end
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::new();
            v.push(0);
            for _ in 1..(n-1) { v.push(rng.gen_i32(0, 10_000)); }
            v.push(10_000);
            v
        }
        _ => {
            // zig-zag
            let n = rng.gen_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { (t as i32 % 10_000) } else { ((t as i32 * 3 + 1) % 10_000) });
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
        let raw = build(mode, &mut rng, t);
        if raw.is_empty() || raw.len() > 100_000 { continue; }
        let mut ok = true;
        for &x in &raw {
            if x < 0 || x > 10_000 { ok = false; break; }
        }
        if !ok { continue; }
        let prices = generate_test_case(&raw);
        print_json(&prices);
    }
}