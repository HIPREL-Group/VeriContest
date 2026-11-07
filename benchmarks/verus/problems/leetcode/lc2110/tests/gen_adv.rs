use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (prices: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= prices.len() <= 100_000,
        forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100_000,
        prices.len() == values.len(),
        forall |i: int| 0 <= i < prices.len() ==> prices[i] == values[i],
{
    let n = values.len();
    let mut prices: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            prices.len() == i,
            forall |k: int| 0 <= k < i as int ==> prices[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] prices[k] <= 100_000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
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
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100_000));
    }
    v
}

fn build_descending(rng: &mut Rng, n: usize) -> Vec<i32> {
    // long smooth descent
    let start = rng.gen_range_i32(n as i32, 100_000);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(start - i as i32);
    }
    v
}

fn build_ascending(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((i + 1) as i32);
    }
    v
}

fn build_constant(rng: &mut Rng, n: usize) -> Vec<i32> {
    let c = rng.gen_range_i32(1, 100_000);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(c);
    }
    v
}

fn build_segments(rng: &mut Rng, n: usize) -> Vec<i32> {
    // alternating descent segments
    let mut v = Vec::with_capacity(n);
    let mut i = 0;
    while i < n {
        let seg_len = rng.gen_range_usize(1, 20).min(n - i);
        let start = rng.gen_range_i32(seg_len as i32, 100_000);
        for k in 0..seg_len {
            v.push(start - k as i32);
        }
        i += seg_len;
    }
    v
}

fn build_diff_not_one(rng: &mut Rng, n: usize) -> Vec<i32> {
    // differences of 2 (not smooth)
    let mut v = Vec::with_capacity(n);
    let start = rng.gen_range_i32((2 * n as i32).min(100_000), 100_000);
    for i in 0..n {
        let val = start - 2 * i as i32;
        v.push(if val < 1 { 1 } else { val });
    }
    v
}

fn build_single_value(rng: &mut Rng, low: bool) -> Vec<i32> {
    let v = if low { 1 } else { 100_000 };
    let _ = rng.next_u64();
    vec![v]
}

fn build_edge_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let choice = rng.next_u64() % 4;
        let val = match choice {
            0 => 1,
            1 => 100_000,
            2 => 2,
            _ => 99_999,
        };
        v.push(val);
    }
    v
}

fn build_near_wrap(n: usize) -> Vec<i32> {
    // start high, descend into low
    let start = 100_000;
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let val = start - i as i32;
        v.push(if val < 1 { 1 } else { val });
    }
    v
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(1, 50),
            3 => rng.gen_range_usize(50, 500),
            4 => 100_000,
            5 => rng.gen_range_usize(1, 1000),
            6 => rng.gen_range_usize(2, 100),
            7 => rng.gen_range_usize(100, 10_000),
            8 => 50_000,
            9 => rng.gen_range_usize(3, 300),
            _ => rng.gen_range_usize(1, 200),
        };

        let values: Vec<i32> = match mode {
            0 => build_single_value(&mut rng, t % 2 == 0),
            1 => build_random(&mut rng, n),
            2 => build_descending(&mut rng, n),
            3 => build_ascending(n),
            4 => {
                // avoid huge descending that goes below 1; cap n
                let nn = n.min(99_999);
                build_descending(&mut rng, nn)
            }
            5 => build_constant(&mut rng, n),
            6 => build_segments(&mut rng, n),
            7 => build_diff_not_one(&mut rng, n),
            8 => build_random(&mut rng, n),
            9 => build_edge_values(&mut rng, n),
            _ => {
                if t % 3 == 0 {
                    build_near_wrap(n.min(100_000))
                } else {
                    build_segments(&mut rng, n)
                }
            }
        };

        // Verify constraints before calling
        if values.is_empty() || values.len() > 100_000 {
            continue;
        }
        let mut ok = true;
        for &v in &values {
            if v < 1 || v > 100_000 { ok = false; break; }
        }
        if !ok { continue; }

        let prices = generate_test_case(&values);
        print_json(&prices);
    }
}