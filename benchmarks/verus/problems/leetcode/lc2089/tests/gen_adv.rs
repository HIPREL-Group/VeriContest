use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums: Vec<i32>, target: i32) -> (result: (Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    let nums = bounded_values(&nums);
    let target = if target < 1 { 1 } else if target > 100 { 100 } else { target };
    (nums, target)
}


pub open spec fn count_eq_prefix(s: Seq<i32>, target: i32, n: nat) -> int
    decreases n,
{
    if n == 0 {
        0int
    } else {
        count_eq_prefix(s, target, (n - 1) as nat)
            + (if s[(n - 1) as int] == target { 1int } else { 0int })
    }
}

pub fn generate_candidate(
    nums: Vec<i32>,
    target: i32,
) -> (result: (Vec<i32>, i32))
    requires
        nums.len() >= 1,
        nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= target <= 100,
    ensures
        result.0.len() <= 2147483647usize,
        result.0.len() == nums.len(),
        result.1 == target,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
{
    (nums, target)
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

fn build_nums(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn print_json(nums: &[i32], target: i32) {
    let (nums, target) = generate_test_case(nums.to_vec(), target);
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let (nums, target): (Vec<i32>, i32) = match mode {
            0 => {
                // Single element
                let x = rng.gen_range_i32(1, 100);
                let target = rng.gen_range_i32(1, 100);
                (vec![x], target)
            }
            1 => {
                // Max size, all target
                let target = rng.gen_range_i32(1, 100);
                let v = vec![target; 100];
                (v, target)
            }
            2 => {
                // Target not present (all 1s, target 100)
                (vec![1i32; 50], 100)
            }
            3 => {
                // Target = 1, mix
                let n = rng.gen_range_usize(1, 100);
                (build_nums(&mut rng, n, 1, 3), 1)
            }
            4 => {
                // Target = 100, mix
                let n = rng.gen_range_usize(1, 100);
                (build_nums(&mut rng, n, 98, 100), 100)
            }
            5 => {
                // All distinct values 1..n
                let n = rng.gen_range_usize(1, 100);
                let mut v = Vec::with_capacity(n);
                for i in 0..n { v.push((i as i32) + 1); }
                let target = rng.gen_range_i32(1, n as i32);
                (v, target)
            }
            6 => {
                // Two values
                let n = rng.gen_range_usize(2, 100);
                let a = rng.gen_range_i32(1, 100);
                let b = rng.gen_range_i32(1, 100);
                let mut v = Vec::with_capacity(n);
                for i in 0..n {
                    v.push(if i % 2 == 0 { a } else { b });
                }
                (v, a)
            }
            7 => {
                // Target appears at boundary positions
                let n = rng.gen_range_usize(3, 100);
                let target = rng.gen_range_i32(1, 100);
                let other = if target == 1 { 2 } else { 1 };
                let mut v = vec![other; n];
                v[0] = target;
                v[n-1] = target;
                (v, target)
            }
            8 => {
                // Large n, random
                let n = rng.gen_range_usize(50, 100);
                let target = rng.gen_range_i32(1, 10);
                (build_nums(&mut rng, n, 1, 10), target)
            }
            9 => {
                // Small n, random
                let n = rng.gen_range_usize(1, 5);
                let target = rng.gen_range_i32(1, 100);
                (build_nums(&mut rng, n, 1, 100), target)
            }
            _ => {
                // fully random
                let n = rng.gen_range_usize(1, 100);
                let target = rng.gen_range_i32(1, 100);
                (build_nums(&mut rng, n, 1, 100), target)
            }
        };

        let (out_nums, out_target) = generate_candidate(nums, target);
        print_json(&out_nums, out_target);
    }
}
