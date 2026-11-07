use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        fillers.len() <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> -100_000 <= #[trigger] fillers[i] <= 100_000,
    ensures
        nums.len() <= 2147483647usize,
        nums.len() == fillers.len(),
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let n = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    while pos < n
        invariant
            n == fillers.len(),
            n <= 100,
            pos <= n,
            nums.len() == pos,
            forall|i: int| 0 <= i < fillers.len() ==> -100_000 <= #[trigger] fillers[i] <= 100_000,
            forall|k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == fillers[k],
        decreases n - pos,
    {
        nums.push(fillers[pos]);
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 0.max(1),
        2 => 2,
        3 => 100,
        4 => 3 + (t % 10),
        5 => 50,
        6 => 100,
        7 => 10,
        8 => 100,
        9 => 5 + (t % 20),
        _ => 1 + (t % 100),
    };
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            v.push(rng.gen_i32(-100_000, 100_000));
        }
        1 => {
            let x = rng.gen_i32(-100_000, 100_000);
            for _ in 0..n { v.push(x); }
        }
        2 => {
            v.push(-100_000);
            v.push(100_000);
        }
        3 => {
            let x = rng.gen_i32(-100_000, 100_000);
            for _ in 0..n { v.push(x); }
        }
        4 => {
            v.push(-100_000);
            for _ in 0..(n-2) { v.push(rng.gen_i32(-99_999, 99_999)); }
            v.push(100_000);
        }
        5 => {
            let lo = rng.gen_i32(-100_000, 0);
            let hi = rng.gen_i32(1, 100_000);
            v.push(lo);
            v.push(hi);
            for _ in 2..n {
                if rng.next_u64() % 2 == 0 { v.push(lo); } else { v.push(hi); }
            }
        }
        6 => {
            for i in 0..n { v.push(i as i32); }
        }
        7 => {
            for i in 0..n { v.push(-(i as i32)); }
        }
        8 => {
            for _ in 0..n { v.push(rng.gen_i32(-100_000, 100_000)); }
        }
        9 => {
            let a = rng.gen_i32(-100_000, 100_000);
            let b = rng.gen_i32(-100_000, 100_000);
            for i in 0..n {
                if i % 2 == 0 { v.push(a); } else { v.push(b); }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_i32(-100_000, 100_000)); }
        }
    }
    while v.len() > 100 { v.pop(); }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let fillers = build(&mut rng, mode, t);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}