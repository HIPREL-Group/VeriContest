use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 50_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 50_000,
    ensures
        2 <= nums.len() <= 50_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 50_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 50_000,
            i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 50_000,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_random(rng: &mut Rng, n: usize, maxv: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(0, maxv));
    }
    v
}

fn build_strictly_decreasing(n: usize) -> Vec<i32> {
    // e.g., 50000, 49999, ..., 50000 - n + 1 (all non-negative since n <= 50000)
    let mut v = Vec::with_capacity(n);
    let start: i32 = 50_000;
    for i in 0..n {
        v.push(start - i as i32);
    }
    v
}

fn build_strictly_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(i as i32 % 50_001);
    }
    v
}

fn build_all_same(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn build_two_plateaus(n: usize, a: i32, b: i32) -> Vec<i32> {
    // First half a, second half b (b >= a makes big ramp)
    let mut v = Vec::with_capacity(n);
    let h = n / 2;
    for _ in 0..h { v.push(a); }
    for _ in h..n { v.push(b); }
    v
}

fn build_big_then_small_then_big(n: usize) -> Vec<i32> {
    // Valley: high, low..., high
    let mut v = Vec::with_capacity(n);
    v.push(50_000);
    for _ in 1..n-1 { v.push(0); }
    v.push(50_000);
    v
}

fn build_min_first(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    v.push(0);
    for _ in 1..n {
        v.push(rng.gen_range_i32(0, 50_000));
    }
    v
}

fn build_max_last(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n-1 {
        v.push(rng.gen_range_i32(0, 50_000));
    }
    v.push(50_000);
    v
}

fn build_zigzag(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 { v.push(0); } else { v.push(50_000); }
    }
    v
}

fn build_decreasing_except_tail(n: usize) -> Vec<i32> {
    // decreasing then one equal to nums[0] at the end
    let mut v = build_strictly_decreasing(n);
    if n >= 2 {
        let first = v[0];
        let last = v.len() - 1;
        v[last] = first;
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 2 + (t % 8),
            1 => rng.gen_range_usize(2, 100),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(1000, 5000),
            4 => 50_000,
            5 => rng.gen_range_usize(2, 500),
            6 => rng.gen_range_usize(2, 500),
            7 => rng.gen_range_usize(10, 2000),
            8 => rng.gen_range_usize(2, 200),
            _ => rng.gen_range_usize(2, 1000),
        };

        let values: Vec<i32> = match mode {
            0 => build_random(&mut rng, n, 50_000),
            1 => build_strictly_decreasing(n),
            2 => build_strictly_increasing(n),
            3 => build_all_same(n, rng.gen_range_i32(0, 50_000)),
            4 => {
                // large decreasing - worst case for O(n^2)
                build_strictly_decreasing(n)
            }
            5 => {
                let a = rng.gen_range_i32(0, 50_000);
                let b = rng.gen_range_i32(0, 50_000);
                build_two_plateaus(n, a, b)
            }
            6 => build_big_then_small_then_big(n),
            7 => build_min_first(n, &mut rng),
            8 => build_max_last(n, &mut rng),
            9 => build_zigzag(n),
            _ => build_decreasing_except_tail(n),
        };

        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}