use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range(1, 10_000));
    }
    v
}

fn build_all_equal(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn build_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn build_small_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range(1, 3));
    }
    v
}

fn build_max_values(n: usize) -> Vec<i32> {
    build_all_equal(n, 10_000)
}

fn build_single_peak(n: usize, peak_idx: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i == peak_idx { 10_000 } else { 1 });
    }
    v
}

fn build_fair_with_one_removal(rng: &mut Rng, n: usize) -> Vec<i32> {
    // start with all ones, the answer structure varies
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range(1, 100));
    }
    v
}

fn build_sequential(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(((i % 10_000) + 1) as i32);
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
        let mode = t % 10;
        let values = match mode {
            0 => {
                // small random
                let n = rng.gen_range_usize(1, 20);
                build_random(&mut rng, n)
            }
            1 => {
                // n=1
                vec![rng.gen_range(1, 10_000)]
            }
            2 => {
                // all equal
                let n = rng.gen_range_usize(2, 100);
                build_all_equal(n, rng.gen_range(1, 10_000))
            }
            3 => {
                // alternating
                let n = rng.gen_range_usize(2, 100);
                build_alternating(n, rng.gen_range(1, 10_000), rng.gen_range(1, 10_000))
            }
            4 => {
                // small values
                let n = rng.gen_range_usize(1, 500);
                build_small_values(&mut rng, n)
            }
            5 => {
                // max values
                let n = rng.gen_range_usize(1, 1000);
                build_max_values(n)
            }
            6 => {
                // single peak
                let n = rng.gen_range_usize(2, 200);
                let p = rng.gen_range_usize(0, n - 1);
                build_single_peak(n, p)
            }
            7 => {
                // random medium
                let n = rng.gen_range_usize(50, 500);
                build_fair_with_one_removal(&mut rng, n)
            }
            8 => {
                // sequential
                let n = rng.gen_range_usize(1, 1000);
                build_sequential(n)
            }
            _ => {
                // large
                let n = if t % 20 == 9 { 100_000 } else { rng.gen_range_usize(1000, 5000) };
                build_random(&mut rng, n)
            }
        };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}