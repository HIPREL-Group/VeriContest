use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> -1_000_000 <= #[trigger] values[i] <= 1_000_000,
    ensures
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -1_000_000 <= #[trigger] values[k] <= 1_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -1_000_000 <= #[trigger] nums[k] <= 1_000_000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all max positive
            for _ in 0..n { v.push(1_000_000); }
        }
        1 => {
            // all max negative
            for _ in 0..n { v.push(-1_000_000); }
        }
        2 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        3 => {
            // alternating max/-max
            for i in 0..n { v.push(if i % 2 == 0 { 1_000_000 } else { -1_000_000 }); }
        }
        4 => {
            // small examples pattern [1,2,3,4...]
            for i in 0..n { v.push((i as i32 % 1000) + 1); }
        }
        5 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        6 => {
            // descending
            for i in 0..n { v.push(1_000_000 - (i as i32 % 1_000_000)); }
        }
        7 => {
            // random small
            for _ in 0..n { v.push(rng.gen_range_i32(-10, 10)); }
        }
        8 => {
            // random full range
            for _ in 0..n { v.push(rng.gen_range_i32(-1_000_000, 1_000_000)); }
        }
        9 => {
            // boundary mix
            for i in 0..n {
                let c = i % 3;
                if c == 0 { v.push(-1_000_000); }
                else if c == 1 { v.push(0); }
                else { v.push(1_000_000); }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(-1_000_000, 1_000_000)); }
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
        let n = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 1000,
            3 => 999,
            4 => 3,
            5 => 10,
            6 => 100,
            7 => 500,
            8 => rng.gen_range_usize(1, 1000),
            9 => rng.gen_range_usize(1, 50),
            10 => rng.gen_range_usize(900, 1000),
            11 => rng.gen_range_usize(1, 10),
            _ => rng.gen_range_usize(1, 1000),
        };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}