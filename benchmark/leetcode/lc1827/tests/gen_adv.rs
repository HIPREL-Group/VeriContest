use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 5000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= nums.len() <= 5000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    nums
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
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
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => vec![rng.gen_i32(1, 10_000)], // singleton
        1 => { // all same value
            let n = rng.gen_usize(2, 100);
            let v = rng.gen_i32(1, 10_000);
            vec![v; n]
        }
        2 => { // all 1s
            let n = rng.gen_usize(1, 5000);
            vec![1i32; n]
        }
        3 => { // strictly decreasing from 10000
            let n = rng.gen_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                let x = 10_000i32 - (i as i32 % 10_000);
                v.push(if x < 1 { 1 } else { x });
            }
            v
        }
        4 => { // already strictly increasing
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::new();
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur = if cur < 10_000 { cur + 1 } else { 10_000 };
            }
            v
        }
        5 => { // max length all same
            vec![5000i32; 5000]
        }
        6 => { // max length ones
            vec![1i32; 5000]
        }
        7 => { // max length max values
            vec![10_000i32; 5000]
        }
        8 => { // alternating
            let n = rng.gen_usize(2, 500);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 10_000 });
            }
            v
        }
        9 => { // random small values
            let n = rng.gen_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(1, 10)); }
            v
        }
        10 => { // random full range
            let n = rng.gen_usize(1, 5000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(1, 10_000)); }
            v
        }
        11 => { // boundary 10_000
            let n = rng.gen_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 3 == 0 { 10_000 } else { rng.gen_i32(1, 10_000) });
            }
            v
        }
        _ => {
            let n = rng.gen_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(1, 100)); }
            v
        }
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 13usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode, t);
        if values.is_empty() || values.len() > 5000 { continue; }
        let mut ok = true;
        for &x in &values { if x < 1 || x > 10_000 { ok = false; break; } }
        if !ok { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}