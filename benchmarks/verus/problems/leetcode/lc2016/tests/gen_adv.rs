use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        nums.len() == values.len(),
        forall |i: int| 0 <= i < nums.len() ==> nums[i] == values[i],
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn build_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut x: i32 = 1_000_000_000;
    for _ in 0..n {
        v.push(x);
        if x > 1 { x -= 1; }
    }
    v
}

fn build_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((i as i32) + 1);
    }
    v
}

fn build_constant(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn build_v_shape(n: usize) -> Vec<i32> {
    // decreasing then increasing
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..mid {
        v.push((mid - i) as i32 + 1);
    }
    for i in mid..n {
        v.push((i - mid + 1) as i32);
    }
    v
}

fn build_peak(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..mid {
        v.push((i + 1) as i32);
    }
    for i in mid..n {
        v.push((n - i) as i32);
    }
    v
}

fn build_big_drop_small_rise(n: usize) -> Vec<i32> {
    // first half huge values, second half small values with tiny increase
    let mut v = Vec::with_capacity(n);
    let half = n / 2;
    for _ in 0..half {
        v.push(1_000_000_000);
    }
    for i in half..n {
        v.push(1 + (i - half) as i32);
    }
    v
}

fn build_two_elements(a: i32, b: i32) -> Vec<i32> {
    vec![a, b]
}

fn build_max_diff_at_ends(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    v.push(1);
    for _ in 1..(n-1) {
        v.push(500_000_000);
    }
    v.push(1_000_000_000);
    v
}

fn build_max_diff_needs_global(n: usize) -> Vec<i32> {
    // min at start, max at end, but lots of noise
    let mut v = Vec::with_capacity(n);
    v.push(1);
    for i in 1..(n-1) {
        v.push(((i * 7) % 999 + 2) as i32);
    }
    v.push(1_000_000_000);
    v
}

fn clamp_values(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 12;
        let n = match mode {
            0 => 2,
            1 => 1000,
            2 => 3,
            3 => rng.gen_range_usize(2, 20),
            4 => rng.gen_range_usize(2, 1000),
            5 => 1000,
            6 => rng.gen_range_usize(4, 100),
            7 => rng.gen_range_usize(2, 50),
            8 => 2,
            9 => 1000,
            10 => rng.gen_range_usize(2, 500),
            _ => rng.gen_range_usize(2, 200),
        };

        let mut v = match mode {
            0 => build_random(&mut rng, n, 1, 1_000_000_000),
            1 => build_decreasing(n),
            2 => build_increasing(n),
            3 => {
                let val = rng.gen_range_i32(1, 1_000_000_000);
                build_constant(n, val)
            }
            4 => build_v_shape(n),
            5 => build_peak(n),
            6 => build_big_drop_small_rise(n),
            7 => build_random(&mut rng, n, 1, 10),
            8 => {
                let a = rng.gen_range_i32(1, 1_000_000_000);
                let b = rng.gen_range_i32(1, 1_000_000_000);
                build_two_elements(a, b)
            }
            9 => build_max_diff_at_ends(n),
            10 => build_max_diff_needs_global(n),
            _ => build_random(&mut rng, n, 1, 1_000_000_000),
        };

        clamp_values(&mut v);
        // Ensure length bounds.
        if v.len() < 2 {
            v.push(1);
            v.push(2);
        }
        if v.len() > 1000 {
            v.truncate(1000);
        }

        let nums = generate_test_case(&v);
        print_json(&nums);
    }
}