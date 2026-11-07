use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 2_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= nums.len() <= 2_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 100_000,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 100_000);
        nums.push(v);
        i = i + 1;
    }
    nums
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

fn build(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small all odd
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                let mut x = rng.gen_range_i32(1, 100_000);
                if x % 2 == 0 { x += 1; if x > 100_000 { x -= 2; } }
                v.push(x);
            }
            v
        }
        1 => {
            // small all even
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                let mut x = rng.gen_range_i32(1, 100_000);
                if x % 2 == 1 { x += 1; if x > 100_000 { x -= 2; } }
                v.push(x);
            }
            v
        }
        2 => {
            // single element
            let x = rng.gen_range_i32(1, 100_000);
            vec![x]
        }
        3 => {
            // tie between two even numbers
            let mut a = rng.gen_range_i32(2, 100_000);
            if a % 2 == 1 { a -= 1; if a < 2 { a = 2; } }
            let mut b = rng.gen_range_i32(2, 100_000);
            if b % 2 == 1 { b -= 1; if b < 2 { b = 2; } }
            if a == b { b = if b + 2 <= 100_000 { b + 2 } else { b - 2 }; }
            let mut v = Vec::new();
            let c = rng.gen_range_usize(1, 20);
            for _ in 0..c { v.push(a); v.push(b); }
            v
        }
        4 => {
            // max length random
            let n = 2000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
            v
        }
        5 => {
            // all same even
            let mut x = rng.gen_range_i32(2, 100_000);
            if x % 2 == 1 { x -= 1; }
            let n = rng.gen_range_usize(1, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        6 => {
            // all same odd
            let mut x = rng.gen_range_i32(1, 100_000);
            if x % 2 == 0 { x += 1; if x > 100_000 { x -= 2; } }
            let n = rng.gen_range_usize(1, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        7 => {
            // boundary values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                let c = rng.gen_range_usize(0, 3);
                let x = match c {
                    0 => 1,
                    1 => 2,
                    2 => 100_000,
                    _ => 99_999,
                };
                v.push(x);
            }
            v
        }
        8 => {
            // many small values with one most frequent even
            let n = rng.gen_range_usize(10, 500);
            let mut v = Vec::new();
            let freq_val = {
                let mut x = rng.gen_range_i32(2, 100);
                if x % 2 == 1 { x -= 1; if x < 2 { x = 2; } }
                x
            };
            for _ in 0..(n/2) { v.push(freq_val); }
            for _ in 0..(n - n/2) {
                v.push(rng.gen_range_i32(1, 100_000));
            }
            v
        }
        9 => {
            // length 2
            let a = rng.gen_range_i32(1, 100_000);
            let b = rng.gen_range_i32(1, 100_000);
            vec![a, b]
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100_000)); }
            let _ = t;
            v
        }
    }
}

fn sanitize(v: Vec<i32>) -> Vec<i32> {
    let mut r = Vec::with_capacity(v.len());
    for x in v {
        let mut y = x;
        if y < 1 { y = 1; }
        if y > 100_000 { y = 100_000; }
        r.push(y);
    }
    if r.is_empty() { r.push(1); }
    if r.len() > 2000 { r.truncate(2000); }
    r
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = build(mode, &mut rng, t);
        let values = sanitize(raw);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}