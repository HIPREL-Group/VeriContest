use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 50_000,
        forall|i: int| 0 <= i < values.len() ==> -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> -1_000_000_000 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 50_000,
        4 => rng.gen_range_usize(1, 20),
        5 => rng.gen_range_usize(100, 500),
        6 => rng.gen_range_usize(1000, 5000),
        7 => 50_000,
        8 => rng.gen_range_usize(3, 100),
        9 => rng.gen_range_usize(3, 300),
        _ => rng.gen_range_usize(1, 1000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 => {
            v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
        }
        1 => {
            let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            v.push(x);
            v.push(x);
        }
        2 => {
            v.push(1); v.push(2); v.push(3);
        }
        3 => {
            // Large all same
            let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            for _ in 0..n { v.push(x); }
        }
        4 => {
            // small random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
        }
        5 => {
            // Two majority candidates
            let a = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            let mut b = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            if b == a { b = a.wrapping_add(1); if b < -1_000_000_000 || b > 1_000_000_000 { b = a - 1; } }
            let ca = n * 2 / 5;
            let cb = n * 2 / 5;
            for _ in 0..ca { v.push(a); }
            for _ in 0..cb { v.push(b); }
            while v.len() < n {
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                v.push(x);
            }
        }
        6 => {
            // Boyer-Moore trap: alternating with filler
            let a: i32 = 1;
            let b: i32 = 2;
            let c: i32 = 3;
            for i in 0..n {
                match i % 3 {
                    0 => v.push(a),
                    1 => v.push(b),
                    _ => v.push(c),
                }
            }
        }
        7 => {
            // Large size with extremes
            for i in 0..n {
                if i % 2 == 0 { v.push(1_000_000_000); } else { v.push(-1_000_000_000); }
            }
        }
        8 => {
            // One true majority
            let x = rng.gen_range_i32(-100, 100);
            let cnt = n / 2 + 1;
            for _ in 0..cnt { v.push(x); }
            while v.len() < n {
                let y = rng.gen_range_i32(-1000, 1000);
                v.push(y);
            }
        }
        9 => {
            // No majority
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
        _ => {
            let bound = if t % 3 == 0 { 10 } else if t % 3 == 1 { 1_000_000 } else { 1_000_000_000 };
            for _ in 0..n {
                v.push(rng.gen_range_i32(-bound, bound));
            }
        }
    }

    // Shuffle a bit
    let len = v.len();
    if len > 1 {
        for _ in 0..(len / 2) {
            let i = rng.gen_range_usize(0, len - 1);
            let j = rng.gen_range_usize(0, len - 1);
            v.swap(i, j);
        }
    }

    // Clamp to range
    for i in 0..v.len() {
        if v[i] < -1_000_000_000 { v[i] = -1_000_000_000; }
        if v[i] > 1_000_000_000 { v[i] = 1_000_000_000; }
    }

    if v.is_empty() { v.push(0); }

    v
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}