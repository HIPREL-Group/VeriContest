use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 10_000,
        forall|i: int| 0 <= i < vals.len() ==> i32::MIN <= #[trigger] vals[i] <= i32::MAX,
    ensures
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> i32::MIN <= #[trigger] nums[i] <= i32::MAX,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = vals.len();
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall|k: int| 0 <= k < vals.len() ==> i32::MIN <= #[trigger] vals[k] <= i32::MAX,
        decreases n - i,
    {
        nums.push(vals[i]);
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

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn build_and_print(vals: Vec<i32>) {
    let nums = generate_test_case(&vals);
    print_json(&nums);
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // tiny random small-range
            let n = rng.gen_range_usize(1, 6);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_i32(-5, 5));
            }
            v
        }
        1 => {
            // single element
            vec![rng.gen_i32(i32::MIN, i32::MAX)]
        }
        2 => {
            // two elements
            vec![rng.gen_i32(-10, 10), rng.gen_i32(-10, 10)]
        }
        3 => {
            // all same
            let x = rng.gen_i32(-100, 100);
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        4 => {
            // only two distinct values
            let a = rng.gen_i32(-100, 100);
            let b = rng.gen_i32(-100, 100);
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
            v
        }
        5 => {
            // extremes including i32::MIN and i32::MAX
            let choices = [i32::MIN, i32::MAX, 0, -1, 1, i32::MIN + 1, i32::MAX - 1];
            let n = rng.gen_range_usize(3, 15);
            let mut v = Vec::new();
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, choices.len() - 1);
                v.push(choices[idx]);
            }
            v
        }
        6 => {
            // sorted ascending distinct
            let n = rng.gen_range_usize(3, 50);
            let start = rng.gen_i32(-1000, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(start + i as i32);
            }
            v
        }
        7 => {
            // sorted descending
            let n = rng.gen_range_usize(3, 50);
            let start = rng.gen_i32(-1000, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(start - i as i32);
            }
            v
        }
        8 => {
            // large size
            let n = if t % 2 == 0 { 10_000 } else { 9_999 };
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_i32(-100, 100));
            }
            v
        }
        9 => {
            // exactly 3 distinct with duplicates
            let a = rng.gen_i32(-1000, 1000);
            let b = rng.gen_i32(-1000, 1000);
            let c = rng.gen_i32(-1000, 1000);
            let n = rng.gen_range_usize(3, 30);
            let mut v = Vec::new();
            let choices = [a, b, c];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, 2);
                v.push(choices[idx]);
            }
            v
        }
        _ => {
            // random general
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_i32(i32::MIN, i32::MAX));
            }
            v
        }
    }
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

    // Fixed edge cases
    build_and_print(vec![3, 2, 1]);
    build_and_print(vec![1, 2]);
    build_and_print(vec![2, 2, 3, 1]);
    build_and_print(vec![1]);
    build_and_print(vec![i32::MIN]);
    build_and_print(vec![i32::MAX]);
    build_and_print(vec![i32::MIN, i32::MAX]);
    build_and_print(vec![i32::MIN, i32::MIN + 1, i32::MAX]);
    build_and_print(vec![1, 1, 1, 1]);
    build_and_print(vec![5, 5, 4, 4, 3, 3]);

    for t in 0..total {
        let mode = t % modes;
        let vals = gen_mode(&mut rng, mode, t);
        build_and_print(vals);
    }
}