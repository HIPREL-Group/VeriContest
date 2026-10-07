use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> -100000 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> -100000 <= #[trigger] nums[i] <= 100000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -100000 <= #[trigger] values[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -100000 <= #[trigger] nums[k] <= 100000,
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
        Self { state: seed.wrapping_add(1) }
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

fn clamp_vec(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x < -100000 { *x = -100000; }
        if *x > 100000 { *x = 100000; }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn make_test(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(3, 20),
        3 => rng.gen_range_usize(50, 200),
        4 => 100000,
        5 => rng.gen_range_usize(10, 100),
        6 => rng.gen_range_usize(5, 50),
        7 => rng.gen_range_usize(3, 30),
        8 => rng.gen_range_usize(100, 1000),
        9 => rng.gen_range_usize(2, 10),
        _ => rng.gen_range_usize(1, 500),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 | 1 => {
            for _ in 0..n { v.push(rng.gen_range_i32(-100000, 100000)); }
        }
        2 => {
            // strictly increasing
            let mut cur = rng.gen_range_i32(-100000, -50000);
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(1, 100));
            }
        }
        3 => {
            // non-decreasing
            let mut cur = rng.gen_range_i32(-100000, 0);
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(0, 5));
            }
        }
        4 => {
            // non-increasing (large)
            let mut cur: i32 = 100000;
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_sub(rng.gen_range_i32(0, 2));
            }
        }
        5 => {
            // strictly decreasing
            let mut cur = rng.gen_range_i32(50000, 100000);
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_sub(rng.gen_range_i32(1, 100));
            }
        }
        6 => {
            // constant
            let c = rng.gen_range_i32(-100000, 100000);
            for _ in 0..n { v.push(c); }
        }
        7 => {
            // monotone with a single violation
            let mut cur = rng.gen_range_i32(-100000, 0);
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(1, 50));
            }
            if n >= 2 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = rng.gen_range_i32(-100000, 100000);
            }
        }
        8 => {
            // up then down (not monotonic unless small)
            let half = n / 2;
            let mut cur = rng.gen_range_i32(-100000, 0);
            for _ in 0..half {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(0, 10));
            }
            for _ in half..n {
                v.push(cur);
                cur = cur.saturating_sub(rng.gen_range_i32(0, 10));
            }
        }
        9 => {
            // extremes
            for i in 0..n {
                if (i + t) % 2 == 0 {
                    v.push(100000);
                } else {
                    v.push(-100000);
                }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(-100000, 100000)); }
        }
    }

    clamp_vec(&mut v);
    if v.is_empty() { v.push(0); }
    if v.len() > 100000 { v.truncate(100000); }
    v
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
        let values = make_test(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}