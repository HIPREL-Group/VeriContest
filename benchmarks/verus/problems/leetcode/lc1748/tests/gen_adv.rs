use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            1 <= n <= 100,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => {
            // all same
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(1, 100);
            vec![v; n]
        }
        1 => {
            // all distinct increasing
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i % 100) as i32 + 1);
            }
            v
        }
        2 => {
            // pairs
            let n = rng.gen_range_usize(1, 50) * 2;
            let n = n.min(100).max(1);
            let mut v = Vec::new();
            let mut i = 0;
            while i < n {
                let x = rng.gen_range_i32(1, 100);
                v.push(x);
                if v.len() < n {
                    v.push(x);
                }
                i = v.len();
            }
            v
        }
        3 => {
            // single element
            vec![rng.gen_range_i32(1, 100)]
        }
        4 => {
            // max length, all random
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        5 => {
            // min boundary values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(1i32);
            }
            v
        }
        6 => {
            // max boundary values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(100i32);
            }
            v
        }
        7 => {
            // mix of 1s and 100s
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 });
            }
            v
        }
        8 => {
            // triples of each value
            let n = rng.gen_range_usize(1, 33) * 3;
            let n = n.min(100).max(1);
            let mut v = Vec::new();
            let mut cur: i32 = 1;
            while v.len() < n {
                v.push(cur);
                if v.len() < n { v.push(cur); }
                if v.len() < n { v.push(cur); }
                cur = if cur >= 100 { 1 } else { cur + 1 };
            }
            v
        }
        9 => {
            // one unique among duplicates
            let n = rng.gen_range_usize(3, 100);
            let dup = rng.gen_range_i32(1, 100);
            let uniq = if dup == 100 { 1 } else { dup + 1 };
            let mut v = vec![dup; n];
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = uniq;
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build_values(mode, &mut rng);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}