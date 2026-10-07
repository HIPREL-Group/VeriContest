use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    target: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 10_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
        1 <= target <= 100_000,
    ensures
        1 <= result.0.len() <= 10_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1 <= 100_000,
{
    let mut arr: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            arr.len() == i,
            forall |k: int| 0 <= k < i ==> 1 <= #[trigger] arr[k] <= 100_000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
        decreases n - i,
    {
        arr.push(values[i]);
        i = i + 1;
    }
    (arr, target)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, i32) {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let target: i32;

    match mode {
        0 => {
            // All ones, small target
            for _ in 0..n { v.push(1); }
            target = rng.gen_i32(1, 100_000);
        }
        1 => {
            // All max
            for _ in 0..n { v.push(100_000); }
            target = rng.gen_i32(1, 100_000);
        }
        2 => {
            // Random small values
            for _ in 0..n { v.push(rng.gen_i32(1, 10)); }
            target = rng.gen_i32(1, 100_000);
        }
        3 => {
            // Random full range
            for _ in 0..n { v.push(rng.gen_i32(1, 100_000)); }
            target = rng.gen_i32(1, 100_000);
        }
        4 => {
            // Example 1-like
            v.push(4); v.push(9); v.push(3);
            target = 10;
        }
        5 => {
            // Example 3
            v.push(60864); v.push(25176); v.push(27249); v.push(21296); v.push(20204);
            target = 56803;
        }
        6 => {
            // Target smaller than all elements
            for _ in 0..n { v.push(rng.gen_i32(50_000, 100_000)); }
            target = rng.gen_i32(1, 100);
        }
        7 => {
            // Target much larger than sum could be
            for _ in 0..n { v.push(rng.gen_i32(1, 100)); }
            target = 100_000;
        }
        8 => {
            // Sorted ascending
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur = if cur < 100_000 { cur + 1 } else { 100_000 };
            }
            target = rng.gen_i32(1, 100_000);
        }
        9 => {
            // One big element, rest small
            v.push(100_000);
            for _ in 1..n { v.push(rng.gen_i32(1, 10)); }
            target = rng.gen_i32(1, 100_000);
        }
        _ => {
            // Mixed random
            for _ in 0..n { v.push(rng.gen_i32(1, 100_000)); }
            target = rng.gen_i32(1, 100_000);
        }
    }

    // Safety: ensure length & bounds
    if v.is_empty() { v.push(1); }
    if v.len() > 10_000 { v.truncate(10_000); }
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100_000 { *x = 100_000; }
    }
    let t = if target < 1 { 1 } else if target > 100_000 { 100_000 } else { target };
    (v, t)
}

fn print_json(arr: &[i32], value: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"target\":{}}}", value);
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
            0 => 1 + (t % 20),
            1 => 1 + (t % 50),
            2 => 100 + (t % 10),
            3 => 1 + (t % 500),
            4 => 3,
            5 => 5,
            6 => 1 + (t % 100),
            7 => 1 + (t % 100),
            8 => 1 + (t % 1000),
            9 => 1 + (t % 200),
            _ => 1 + (t % 10_000),
        };
        let n = if n < 1 { 1 } else if n > 10_000 { 10_000 } else { n };
        let (values, target) = build_values(&mut rng, mode, n);
        let (arr, tgt) = generate_test_case(&values, target);
        print_json(&arr, tgt);
    }
}