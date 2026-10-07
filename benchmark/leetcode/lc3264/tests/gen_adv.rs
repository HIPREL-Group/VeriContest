use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    k_val: i32,
    mult_val: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= fillers.len() <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
        1 <= k_val <= 10,
        1 <= mult_val <= 5,
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 10,
        1 <= result.2 <= 5,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 100,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i += 1;
    }
    (nums, k_val, mult_val)
}

}

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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i32) {
    let (n, k, mult, filler_kind) = match mode {
        0 => (1usize, 1i32, 1i32, 0usize),
        1 => (1, 10, 5, 1),
        2 => (2, 3, 4, 2),
        3 => (5, 5, 2, 3),
        4 => (100, 10, 5, 4),
        5 => (100, 1, 1, 5),
        6 => (rng.gen_range_usize(1, 100), rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 5), 6),
        7 => (rng.gen_range_usize(1, 10), rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 5), 7),
        8 => (50, 10, 5, 8),
        9 => (rng.gen_range_usize(2, 20), rng.gen_range_i32(5, 10), rng.gen_range_i32(2, 5), 9),
        _ => (rng.gen_range_usize(1, 100), rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 5), 10),
    };
    let mut fillers = Vec::with_capacity(n);
    for i in 0..n {
        let v = match filler_kind {
            0 => 1,
            1 => 100,
            2 => if i == 0 { 1 } else { 2 },
            3 => (i as i32 % 100) + 1,
            4 => rng.gen_range_i32(1, 100),
            5 => 50,
            6 => rng.gen_range_i32(1, 100),
            7 => rng.gen_range_i32(1, 5),
            8 => if i % 3 == 0 { 1 } else if i % 3 == 1 { 50 } else { 100 },
            9 => { let x = rng.gen_range_i32(1, 10); x },
            _ => rng.gen_range_i32(1, 100),
        };
        let v = if v < 1 { 1 } else if v > 100 { 100 } else { v };
        fillers.push(v);
    }
    generate_test_case(&fillers, k, mult)
}

fn print_json(nums: &[i32], k: i32, mult: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{},\"multiplier\":{}}}", k, mult);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (nums, k, mult) = build_case(&mut rng, mode);
        print_json(&nums, k, mult);
    }
}