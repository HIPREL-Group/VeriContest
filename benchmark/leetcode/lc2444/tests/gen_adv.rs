use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    min_k: i32,
    max_k: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        2 <= values.len() <= 100_000,
        1 <= min_k <= 1_000_000,
        1 <= max_k <= 1_000_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000,
    ensures
        2 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000,
        1 <= result.2 <= 1_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1_000_000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 1_000_000);
        nums.push(v);
        i = i + 1;
    }
    (nums, min_k, max_k)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1_000_000 { 1_000_000 } else { v }
}

fn make_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    let n: usize = match mode {
        0 => 2 + (t % 10),
        1 => rng.gen_range_usize(2, 20),
        2 => rng.gen_range_usize(100, 1000),
        3 => rng.gen_range_usize(1000, 10000),
        4 => 100_000,
        5 => 2,
        6 => rng.gen_range_usize(50, 500),
        7 => rng.gen_range_usize(10, 100),
        8 => rng.gen_range_usize(2, 50),
        9 => rng.gen_range_usize(200, 2000),
        _ => rng.gen_range_usize(2, 1000),
    };

    let (min_k, max_k): (i32, i32) = match mode {
        0 => (1, 5),
        1 => (1, 1),
        2 => {
            let a = rng.gen_range_i32(1, 1_000_000);
            let b = rng.gen_range_i32(1, 1_000_000);
            if a <= b { (a, b) } else { (b, a) }
        }
        3 => (1, 1_000_000),
        4 => (500_000, 500_000),
        5 => (1, 1_000_000),
        6 => (10, 20),
        7 => (1, 3),
        8 => {
            let v = rng.gen_range_i32(2, 999_999);
            (v, v)
        }
        9 => (1, 2),
        _ => (1, 100),
    };

    let mut values: Vec<i32> = Vec::with_capacity(n);
    for idx in 0..n {
        let v = match mode {
            0 => {
                let choices = [1i32, 3, 5, 2, 7, 5];
                choices[idx % choices.len()]
            }
            1 => 1,
            2 => {
                let r = rng.gen_range_i32(1, 1_000_000);
                r
            }
            3 => {
                let r = (rng.next_u64() % 3) as i32;
                if r == 0 { min_k }
                else if r == 1 { max_k }
                else { rng.gen_range_i32(1, 1_000_000) }
            }
            4 => {
                let r = (rng.next_u64() % 10) as i32;
                if r < 5 { 500_000 }
                else if r < 7 { clamp_val(499_999) }
                else if r < 9 { clamp_val(500_001) }
                else { rng.gen_range_i32(1, 1_000_000) }
            }
            5 => {
                let r = rng.gen_range_i32(1, 1_000_000);
                r
            }
            6 => {
                let r = (rng.next_u64() % 5) as i32;
                if r == 0 { 10 }
                else if r == 1 { 20 }
                else if r == 2 { 15 }
                else if r == 3 { 5 }
                else { 25 }
            }
            7 => {
                let r = rng.gen_range_i32(1, 4);
                r
            }
            8 => {
                let r = (rng.next_u64() % 4) as i32;
                if r < 2 { min_k }
                else if r == 2 { clamp_val(min_k - 1) }
                else { clamp_val(min_k + 1) }
            }
            9 => {
                let r = (rng.next_u64() % 3) as i32;
                if r == 0 { 1 } else if r == 1 { 2 } else { 3 }
            }
            _ => {
                let r = rng.gen_range_i32(1, 100);
                r
            }
        };
        values.push(clamp_val(v));
    }

    let (nums, mk, xk) = generate_test_case(&values, min_k, max_k);
    (nums, mk, xk)
}

fn print_json(nums: &[i32], min_k: i32, max_k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"min_k\":{},\"max_k\":{}}}", min_k, max_k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (nums, min_k, max_k) = make_case(&mut rng, mode, t);
        print_json(&nums, min_k, max_k);
    }
}