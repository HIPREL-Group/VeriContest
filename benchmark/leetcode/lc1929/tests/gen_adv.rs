use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { v.push(1); } }
        1 => { for _ in 0..n { v.push(1000); } }
        2 => { for i in 0..n { v.push(((i % 1000) + 1) as i32); } }
        3 => { for i in 0..n { v.push((1000 - (i % 1000)) as i32); } }
        4 => { for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 1000 }); } }
        5 => { for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); } }
        6 => { for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); } }
        7 => { for _ in 0..n { v.push(rng.gen_range_i32(990, 1000)); } }
        8 => { for i in 0..n { v.push(if i == 0 { 1000 } else { 1 }); } }
        9 => { for i in 0..n { v.push(if i == n-1 { 1000 } else { 1 }); } }
        _ => { for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); } }
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
            2 => 2 + (t % 10),
            3 => 500,
            4 => 999,
            5 => rng.gen_range_usize(1, 1000),
            6 => rng.gen_range_usize(1, 50),
            7 => 100,
            8 => 1000,
            9 => 1,
            _ => rng.gen_range_usize(1, 1000),
        };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}