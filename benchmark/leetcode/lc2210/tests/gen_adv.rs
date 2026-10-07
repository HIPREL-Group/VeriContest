use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        3 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            3 <= n <= 100,
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
            forall |i: int| 0 <= i < k as int ==> nums[i] == values[i],
            forall |i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 100,
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }
    nums
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v
}

fn build_small_range(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn build_all_equal(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn build_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn build_strict_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(((i % 100) as i32) + 1);
    }
    // ensure strict where possible; wrap at 100 is fine per constraints
    v
}

fn build_strict_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((100 - (i as i32 % 100)).max(1));
    }
    v
}

fn build_plateaus(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Random plateaus of random lengths
    let mut v = Vec::with_capacity(n);
    while v.len() < n {
        let val = rng.gen_range_i32(1, 10);
        let len = rng.gen_range_usize(1, 5);
        for _ in 0..len {
            if v.len() < n {
                v.push(val);
            }
        }
    }
    v
}

fn build_zigzag(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { 5 } else { 7 });
    }
    v
}

fn build_single_hill(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..n {
        let d = if i > mid { i - mid } else { mid - i };
        let val = (50i32 - d as i32).max(1);
        v.push(val);
    }
    v
}

fn build_single_valley(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..n {
        let d = if i > mid { i - mid } else { mid - i };
        let val = (1i32 + d as i32).min(100);
        v.push(val);
    }
    v
}

fn build_plateau_hill(n: usize) -> Vec<i32> {
    // Something like [1,5,5,5,1,1,...]
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i == 0 || i == n - 1 {
            v.push(1);
        } else if i < n / 2 {
            v.push(5);
        } else {
            v.push(2);
        }
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 12;
        let n = match mode {
            0 => 3,
            1 => 100,
            2 => rng.gen_range_usize(3, 100),
            _ => rng.gen_range_usize(3, 100),
        };
        let values = match mode {
            0 => build_random(&mut rng, n),
            1 => build_random(&mut rng, n),
            2 => build_all_equal(n, rng.gen_range_i32(1, 100)),
            3 => build_alternating(n, rng.gen_range_i32(1, 50), rng.gen_range_i32(51, 100)),
            4 => build_strict_increasing(n),
            5 => build_strict_decreasing(n),
            6 => build_plateaus(&mut rng, n),
            7 => build_zigzag(n),
            8 => build_single_hill(n),
            9 => build_single_valley(n),
            10 => build_plateau_hill(n),
            _ => build_small_range(&mut rng, n, 1, 3),
        };
        // Ensure bounds hold (they do by construction, but clamp defensively).
        let clamped: Vec<i32> = values.iter().map(|&x| x.max(1).min(100)).collect();
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}