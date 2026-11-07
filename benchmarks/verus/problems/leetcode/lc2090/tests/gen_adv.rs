use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>, k: i32) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 100_000,
        0 <= k <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 100_000,
        result.1 == k,
        result.0.len() == values.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            n == values.len(),
            nums.len() == idx,
            forall |i: int| 0 <= i < idx as int ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall |i: int| 0 <= i < idx as int ==> nums[i] == values[i],
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
        decreases n - idx,
    {
        nums.push(values[idx]);
        idx = idx + 1;
    }
    (nums, k)
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

fn build_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { v.push(0); },
        1 => for _ in 0..n { v.push(100_000); },
        2 => for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); },
        3 => for _ in 0..n { v.push(rng.gen_range_i32(0, 10)); },
        4 => for i in 0..n { v.push((i as i32) % 100_001); },
        5 => for i in 0..n { v.push(if i % 2 == 0 { 0 } else { 100_000 }); },
        6 => for i in 0..n { v.push(if i == 0 { 100_000 } else { 0 }); },
        7 => for i in 0..n { v.push(if i == n - 1 { 100_000 } else { 0 }); },
        8 => for _ in 0..n { v.push(1); },
        _ => for _ in 0..n { v.push(rng.gen_range_i32(0, 100_000)); },
    }
    v
}

fn pick_k(rng: &mut Rng, n: usize, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 100_000,
        2 => if n >= 1 { ((n - 1) / 2) as i32 } else { 0 },
        3 => 1,
        4 => if n >= 2 { (n / 2) as i32 } else { 0 },
        5 => if n >= 1 { (n - 1) as i32 } else { 0 },
        6 => rng.gen_range_i32(0, 100_000),
        7 => rng.gen_range_i32(0, if n > 0 { n as i32 } else { 1 }),
        8 => 2,
        _ => rng.gen_range_i32(0, 100_000),
    }
}

fn pick_n(rng: &mut Rng, t: usize, mode: usize) -> usize {
    match mode {
        0 => 1,
        1 => 2,
        2 => 100_000,
        3 => 10,
        4 => 100,
        5 => 1000,
        6 => rng.gen_range_usize(1, 500),
        7 => rng.gen_range_usize(1, 20),
        8 => if t % 2 == 0 { 1 } else { 50_000 },
        _ => rng.gen_range_usize(1, 100_000),
    }
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode_n = (t + (seed as usize)) % modes;
        let mode_v = (t * 3 + 1) % modes;
        let mode_k = (t * 7 + 2) % modes;

        let n = pick_n(&mut rng, t, mode_n);
        let n = if n < 1 { 1 } else if n > 100_000 { 100_000 } else { n };
        let values = build_values(&mut rng, n, mode_v);
        let k_raw = pick_k(&mut rng, n, mode_k);
        let k = if k_raw < 0 { 0 } else if k_raw > 100_000 { 100_000 } else { k_raw };

        let (nums, kk) = generate_test_case(&values, k);
        print_json(&nums, kk);
    }
}