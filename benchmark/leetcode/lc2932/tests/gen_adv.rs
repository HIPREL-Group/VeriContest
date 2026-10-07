use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 50,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
    ensures
        1 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == vals.len(),
            1 <= n <= 50,
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == vals[i],
            forall |i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 100,
        decreases n - k,
    {
        nums.push(vals[k]);
        k = k + 1;
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_vals(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 50,
        3 => rng.gen_range_usize(1, 50),
        4 => rng.gen_range_usize(1, 10),
        5 => 50,
        6 => rng.gen_range_usize(2, 50),
        7 => rng.gen_range_usize(1, 50),
        8 => 50,
        9 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 50),
    };

    let mut v: Vec<i32> = Vec::new();
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => {
                // two close values, potential strong pair
                if i == 0 { rng.gen_range_i32(1, 50) } else {
                    let a = v[0];
                    rng.gen_range_i32(a, (a as i64 * 2).min(100) as i32)
                }
            }
            2 => rng.gen_range_i32(1, 100),
            3 => 1,
            4 => 100,
            5 => {
                // powers of 2
                let powers = [1, 2, 4, 8, 16, 32, 64];
                powers[rng.gen_range_usize(0, 6)]
            }
            6 => {
                // all same value
                if i == 0 { rng.gen_range_i32(1, 100) } else { v[0] }
            }
            7 => {
                // small values only
                rng.gen_range_i32(1, 10)
            }
            8 => {
                // large values only
                rng.gen_range_i32(50, 100)
            }
            9 => {
                // alternating small and large
                if i % 2 == 0 { rng.gen_range_i32(1, 10) } else { rng.gen_range_i32(50, 100) }
            }
            _ => {
                let _ = t;
                rng.gen_range_i32(1, 100)
            }
        };
        let xc = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        v.push(xc);
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
        let vals = build_vals(&mut rng, mode, t);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}