use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 1000,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
            forall |i: int| 0 <= i < pos as int ==> #[trigger] nums[i] == values[i],
            forall |i: int| 0 <= i < pos as int ==> 1 <= #[trigger] nums[i] <= 10_000,
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
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
            for _ in 0..n { v.push(1); }
        }
        1 => {
            for _ in 0..n { v.push(10_000); }
        }
        2 => {
            for i in 0..n { v.push(((i % 10000) + 1) as i32); }
        }
        3 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 9)); }
        }
        4 => {
            for _ in 0..n { v.push(rng.gen_range_i32(10, 99)); }
        }
        5 => {
            for _ in 0..n { v.push(rng.gen_range_i32(100, 999)); }
        }
        6 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1000, 9999)); }
        }
        7 => {
            for i in 0..n {
                let r = rng.next_u64() % 4;
                let x = match r {
                    0 => rng.gen_range_i32(1, 9),
                    1 => rng.gen_range_i32(10, 99),
                    2 => rng.gen_range_i32(100, 999),
                    _ => rng.gen_range_i32(1000, 10000),
                };
                let _ = i;
                v.push(x);
            }
        }
        8 => {
            // alternating extremes
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(10_000); }
            }
        }
        9 => {
            // powers of 10
            let pows = [1i32, 10, 100, 1000, 10000];
            for i in 0..n { v.push(pows[i % 5]); }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10_000)); }
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 1000,
            2 => 1000,
            3 => 2 + (t % 10),
            4 => 10 + (t % 20),
            5 => 50 + (t % 50),
            6 => 100 + (t % 100),
            7 => 500 + (t % 200),
            8 => if t % 2 == 0 { 2 } else { 999 },
            9 => 20 + (t % 30),
            _ => rng.gen_range_usize(1, 1000),
        };
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}