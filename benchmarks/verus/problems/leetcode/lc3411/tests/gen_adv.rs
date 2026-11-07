use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10,
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10,
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

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // all ones
            let n = rng.gen_range_usize(2, 100);
            vec![1; n]
        }
        1 => {
            // all same value > 1
            let n = rng.gen_range_usize(2, 100);
            let v = rng.gen_i32(2, 10);
            vec![v; n]
        }
        2 => {
            // small examples from problem
            vec![1, 2, 1, 2, 1, 1, 1]
        }
        3 => {
            vec![2, 3, 4, 5, 6]
        }
        4 => {
            vec![1, 2, 3, 1, 4, 5, 1]
        }
        5 => {
            // minimal size
            let a = rng.gen_i32(1, 10);
            let b = rng.gen_i32(1, 10);
            vec![a, b]
        }
        6 => {
            // max size, random
            let n = 100;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32(1, 10));
            }
            v
        }
        7 => {
            // primes only
            let primes = [2i32, 3, 5, 7];
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(primes[rng.gen_range_usize(0, 3)]);
            }
            v
        }
        8 => {
            // lots of ones with occasional other
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 4 == 0 {
                    v.push(rng.gen_i32(2, 10));
                } else {
                    v.push(1);
                }
            }
            v
        }
        9 => {
            // alternating pattern
            let n = rng.gen_range_usize(2, 100);
            let a = rng.gen_i32(1, 10);
            let b = rng.gen_i32(1, 10);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
            v
        }
        _ => {
            // fully random
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32(1, 10));
            }
            v
        }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}