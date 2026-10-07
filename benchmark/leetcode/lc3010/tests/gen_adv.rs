use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 50,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
    ensures
        3 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == values.len(),
            3 <= n <= 50,
            0 <= idx <= n,
            nums.len() == idx,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
            forall |i: int| 0 <= i < idx as int ==> #[trigger] nums[i] == values[i],
            forall |i: int| 0 <= i < idx as int ==> 1 <= #[trigger] nums[i] <= 50,
        decreases n - idx,
    {
        nums.push(values[idx]);
        idx = idx + 1;
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 3,
        1 => 50,
        2 => rng.gen_range_usize(3, 5),
        3 => rng.gen_range_usize(3, 50),
        4 => 4,
        5 => rng.gen_range_usize(3, 10),
        6 => 50,
        7 => rng.gen_range_usize(3, 50),
        8 => 3,
        9 => rng.gen_range_usize(3, 50),
        _ => rng.gen_range_usize(3, 50),
    };
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // all same
            let x = rng.gen_i32(1, 50);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // all fifties
            for _ in 0..n { v.push(50); }
        }
        3 => {
            // random
            for _ in 0..n { v.push(rng.gen_i32(1, 50)); }
        }
        4 => {
            // first smallest
            v.push(1);
            for _ in 1..n { v.push(rng.gen_i32(2, 50)); }
        }
        5 => {
            // first largest
            v.push(50);
            for _ in 1..n { v.push(rng.gen_i32(1, 49)); }
        }
        6 => {
            // ascending
            for i in 0..n { v.push(((i % 50) + 1) as i32); }
        }
        7 => {
            // descending
            for i in 0..n { v.push((50 - (i % 50)) as i32); }
        }
        8 => {
            // exactly 3, example-like
            let a = rng.gen_i32(1, 50);
            let b = rng.gen_i32(1, 50);
            let c = rng.gen_i32(1, 50);
            v.push(a); v.push(b); v.push(c);
        }
        9 => {
            // two small at end
            for _ in 0..n { v.push(rng.gen_i32(10, 50)); }
            if n >= 2 {
                let idx1 = rng.gen_range_usize(1, n - 1);
                v[idx1] = 1;
                let idx2 = rng.gen_range_usize(1, n - 1);
                v[idx2] = 1;
            }
        }
        _ => {
            // mixed with duplicates
            let base = rng.gen_i32(1, 25);
            for i in 0..n {
                if i % 2 == 0 { v.push(base); } else { v.push(base + (t as i32 % 25) + 1); }
            }
        }
    }
    // clamp safety
    for i in 0..v.len() {
        if v[i] < 1 { v[i] = 1; }
        if v[i] > 50 { v[i] = 50; }
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
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}