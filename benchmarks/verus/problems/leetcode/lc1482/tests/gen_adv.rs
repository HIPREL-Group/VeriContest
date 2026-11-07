use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000000000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        result.push(if value < 1 { 1 } else if value > 1000000000 { 1000000000 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(bloom_day: Vec<i32>, m: i32, k: i32) -> (result: (Vec<i32>, i32, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
        1 <= result.1 <= 1000000,
        1 <= result.2 <= result.0.len(),
{
    let bloom_day = bounded_values(&bloom_day);
    let m = if m < 1 { 1 } else if m > 1000000 { 1000000 } else { m };
    let k = if k < 1 { 1 } else if k as usize > bloom_day.len() { bloom_day.len() as i32 } else { k };
    (bloom_day, m, k)
}


pub fn generate_candidate(
    bloom: &Vec<i32>,
    day: i32,
    k: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= bloom.len() <= 100_000,
        forall |i: int| 0 <= i < bloom.len() ==> 1 <= #[trigger] bloom[i] <= 1_000_000_000,
        1 <= day <= 1_000_000_000,
        1 <= k <= bloom.len(),
    ensures
        1 <= res.0.len() <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        1 <= res.2 <= res.0.len(),
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < bloom.len()
        invariant
            0 <= i <= bloom.len(),
            out.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] out[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < bloom.len() ==> 1 <= #[trigger] bloom[j] <= 1_000_000_000,
        decreases bloom.len() - i,
    {
        out.push(bloom[i]);
        i += 1;
    }
    (out, day, k)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_bloom(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.range_i32(lo, hi));
    }
    v
}

fn print_case(bloom: &[i32], day: i32, k: i32) {
        let (bloom, day, k) = generate_test_case(bloom.to_vec(), day, k);
    print!("{{\"bloom_day\":[");
    for i in 0..bloom.len() {
        if i > 0 { print!(","); }
        print!("{}", bloom[i]);
    }
    println!("],\"m\":{},\"k\":{}}}", day, k);
}

fn make_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            let n = rng.range_usize(1, 10);
            let bloom = gen_bloom(rng, n, 1, 20);
            let day = rng.range_i32(1, 20);
            let k = rng.range_usize(1, n) as i32;
            (bloom, day, k)
        }
        1 => {
            // large n
            let n = 100_000;
            let bloom = gen_bloom(rng, n, 1, 1_000_000_000);
            let day = rng.range_i32(1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, day, k)
        }
        2 => {
            // k = n
            let n = rng.range_usize(1, 1000);
            let bloom = gen_bloom(rng, n, 1, 1000);
            let day = rng.range_i32(1, 1000);
            (bloom, day, n as i32)
        }
        3 => {
            // k = 1
            let n = rng.range_usize(1, 1000);
            let bloom = gen_bloom(rng, n, 1, 1000);
            let day = rng.range_i32(1, 1000);
            (bloom, day, 1)
        }
        4 => {
            // all same
            let n = rng.range_usize(1, 500);
            let v = rng.range_i32(1, 1_000_000_000);
            let mut bloom = Vec::with_capacity(n);
            for _ in 0..n { bloom.push(v); }
            let day = rng.range_i32(1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, day, k)
        }
        5 => {
            // day = 1, min
            let n = rng.range_usize(1, 100);
            let bloom = gen_bloom(rng, n, 1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, 1, k)
        }
        6 => {
            // day = max
            let n = rng.range_usize(1, 100);
            let bloom = gen_bloom(rng, n, 1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, 1_000_000_000, k)
        }
        7 => {
            // alternating high/low
            let n = rng.range_usize(2, 200);
            let mut bloom = Vec::with_capacity(n);
            for i in 0..n {
                bloom.push(if i % 2 == 0 { 1 } else { 1_000_000_000 });
            }
            let day = rng.range_i32(1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, day, k)
        }
        8 => {
            // n=1
            let bloom = vec![rng.range_i32(1, 1_000_000_000)];
            let day = rng.range_i32(1, 1_000_000_000);
            (bloom, day, 1)
        }
        9 => {
            // bloom near day boundary
            let n = rng.range_usize(1, 500);
            let d = rng.range_i32(2, 1_000_000_000 - 1);
            let mut bloom = Vec::with_capacity(n);
            for _ in 0..n {
                let r = rng.range_i32(0, 2);
                bloom.push(if r == 0 { d - 1 } else if r == 1 { d } else { d + 1 });
            }
            let k = rng.range_usize(1, n) as i32;
            (bloom, d, k)
        }
        _ => {
            let n = rng.range_usize(1, 200) + (t % 50);
            let n = if n > 100_000 { 100_000 } else { n };
            let bloom = gen_bloom(rng, n, 1, 1_000_000_000);
            let day = rng.range_i32(1, 1_000_000_000);
            let k = rng.range_usize(1, n) as i32;
            (bloom, day, k)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (bloom, day, k) = make_case(&mut rng, mode, t);
        // Build Vec<i32> input, call generate_candidate
        let bv: Vec<i32> = bloom.clone();
        let (out, d, kk) = generate_candidate(&bv, day, k);
        print_case(&out, d, kk);
    }
}
