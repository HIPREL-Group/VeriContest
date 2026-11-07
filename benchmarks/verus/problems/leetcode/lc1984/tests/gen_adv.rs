use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    vals: &Vec<i32>,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= n <= 1000,
        1 <= k_val as int <= n as int,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 100_000,
    ensures
        1 <= k_val as int <= res.0.len() <= 1000,
        res.1 == k_val,
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            nums.len() == idx,
            vals.len() == n,
            forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == vals[i],
        decreases n - idx,
    {
        nums.push(vals[idx]);
        idx = idx + 1;
    }
    (nums, k_val)
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_test(mode: usize, rng: &mut Rng) -> (usize, i32, Vec<i32>) {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(1, 100),
        4 => 1000,
        5 => rng.gen_range_usize(500, 1000),
        6 => rng.gen_range_usize(1, 50),
        7 => rng.gen_range_usize(1, 20),
        8 => rng.gen_range_usize(1, 1000),
        9 => rng.gen_range_usize(1, 30),
        _ => rng.gen_range_usize(1, 200),
    };
    let k = match mode {
        0 => 1i32,
        1 => if rng.next_u64() % 2 == 0 { 1 } else { 2 },
        2 => rng.gen_range_i32(1, n as i32),
        3 => rng.gen_range_i32(1, n as i32),
        4 => rng.gen_range_i32(1, 1000),
        5 => n as i32,
        6 => 1,
        7 => n as i32,
        8 => rng.gen_range_i32(1, n as i32),
        9 => rng.gen_range_i32(1, n as i32),
        _ => rng.gen_range_i32(1, n as i32),
    };
    let mut vals: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let v = match mode {
            0 => rng.gen_range_i32(0, 100_000),
            1 => rng.gen_range_i32(0, 100_000),
            2 => rng.gen_range_i32(0, 10),
            3 => rng.gen_range_i32(0, 100_000),
            4 => {
                if i % 2 == 0 { 0 } else { 100_000 }
            }
            5 => 42,
            6 => rng.gen_range_i32(0, 1),
            7 => i as i32,
            8 => 100_000,
            9 => {
                if i == 0 { 0 } else if i == n - 1 { 100_000 } else { rng.gen_range_i32(0, 100_000) }
            }
            _ => rng.gen_range_i32(0, 100_000),
        };
        vals.push(v);
    }
    (n, k, vals)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
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
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, k, vals) = build_test(mode, &mut rng);
        let (nums, kk) = generate_test_case(n, k, &vals);
        print_json(&nums, kk);
    }
}