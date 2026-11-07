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
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
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

fn build_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(1, 100)]
        }
        1 => {
            // all equal, max length
            let v = rng.gen_range_i32(1, 100);
            vec![v; 100]
        }
        2 => {
            // all distinct, length 100 (values 1..=100)
            let mut out = Vec::with_capacity(100);
            for i in 0..100 {
                out.push((i + 1) as i32);
            }
            out
        }
        3 => {
            // length 2, equal
            let v = rng.gen_range_i32(1, 100);
            vec![v, v]
        }
        4 => {
            // length 2, different
            vec![1, 2]
        }
        5 => {
            // small length random
            let n = rng.gen_range_usize(1, 10);
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                out.push(rng.gen_range_i32(1, 100));
            }
            out
        }
        6 => {
            // medium length, few distinct values (many duplicates)
            let n = rng.gen_range_usize(50, 100);
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                out.push(rng.gen_range_i32(1, 3));
            }
            out
        }
        7 => {
            // max length, random
            let mut out = Vec::with_capacity(100);
            for _ in 0..100 {
                out.push(rng.gen_range_i32(1, 100));
            }
            out
        }
        8 => {
            // boundary values 1 and 100
            let n = rng.gen_range_usize(1, 100);
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    out.push(1);
                } else {
                    out.push(100);
                }
            }
            out
        }
        9 => {
            // value 100 repeated
            let n = rng.gen_range_usize(1, 100);
            vec![100; n]
        }
        _ => {
            // general random
            let n = rng.gen_range_usize(1, 100);
            let mut out = Vec::with_capacity(n);
            for _ in 0..n {
                out.push(rng.gen_range_i32(1, 100));
            }
            out
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
        let values = build_case(&mut rng, mode);
        // Ensure preconditions (1..=100 values, length 1..=100)
        let mut valid = true;
        if values.len() < 1 || values.len() > 100 { valid = false; }
        for &v in &values {
            if v < 1 || v > 100 { valid = false; break; }
        }
        if !valid { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}