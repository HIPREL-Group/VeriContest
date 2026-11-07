use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 10_000,
        forall |i: int| 0 <= i < vals.len() ==> -1_000_000_000 <= #[trigger] vals[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < vals.len() ==> #[trigger] vals[i] != -1i32,
    ensures
        1 <= nums.len() <= 10_000,
        nums.len() == vals.len(),
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != -1i32,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> nums[k] == vals[k],
            forall |k: int| 0 <= k < vals.len() ==> -1_000_000_000 <= #[trigger] vals[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < vals.len() ==> #[trigger] vals[k] != -1i32,
        decreases n - i,
    {
        nums.push(vals[i]);
        i += 1;
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_range_i64(lo as i64, hi as i64) as i32
    }
}

fn sanitize(v: i32) -> i32 {
    if v == -1 { 0 } else { v }
}

fn make_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let x = rng.gen_i32(lo, hi);
        v.push(sanitize(x));
    }
    v
}

fn make_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(i as i32);
    }
    v
}

fn make_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((n - i) as i32);
    }
    v
}

fn make_all_same(n: usize, val: i32) -> Vec<i32> {
    let val = sanitize(val);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn make_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let a = sanitize(a);
    let b = sanitize(b);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn make_peak(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..n {
        let d = if i <= mid { i } else { n - i };
        v.push(d as i32);
    }
    v
}

fn make_valley(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..n {
        let d = if i <= mid { mid - i } else { i - mid };
        v.push(d as i32);
    }
    v
}

fn make_extremes(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let c = rng.gen_range_usize(0, 2);
        let x = match c {
            0 => 1_000_000_000i32,
            1 => -1_000_000_000i32,
            _ => 0i32,
        };
        v.push(sanitize(x));
    }
    v
}

fn make_last_greatest(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n - 1 {
        v.push(i as i32);
    }
    v.push(1_000_000_000);
    v
}

fn make_first_greatest(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    v.push(1_000_000_000);
    for i in 1..n {
        v.push(-(i as i32));
    }
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
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 2 + (t % 5),
            2 => 10 + (t % 20),
            3 => 100,
            4 => 10_000,
            5 => rng.gen_range_usize(1, 50),
            6 => rng.gen_range_usize(50, 500),
            7 => rng.gen_range_usize(500, 2000),
            8 => 5000,
            9 => rng.gen_range_usize(2, 30),
            _ => rng.gen_range_usize(1, 1000),
        };

        let vals = match mode {
            0 => make_random(&mut rng, n, -1_000_000_000, 1_000_000_000),
            1 => make_increasing(n),
            2 => make_decreasing(n),
            3 => {
                let val = rng.gen_i32(-1_000_000_000, 1_000_000_000);
                make_all_same(n, val)
            }
            4 => make_extremes(&mut rng, n),
            5 => {
                let a = rng.gen_i32(-100, 100);
                let b = rng.gen_i32(-100, 100);
                make_alternating(n, a, b)
            }
            6 => make_peak(n),
            7 => make_valley(n),
            8 => make_last_greatest(n),
            9 => make_first_greatest(n),
            _ => make_random(&mut rng, n, -100, 100),
        };

        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}