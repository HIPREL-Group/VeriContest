use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
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
        Self { state: seed }
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            let v = rng.gen_range_i32(1, 1000);
            vec![v]
        }
        1 => {
            // all even
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 500) * 2;
                let x = if x > 1000 { 1000 } else { x };
                v.push(x);
            }
            v
        }
        2 => {
            // all odd
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                let x = rng.gen_range_i32(0, 499) * 2 + 1;
                v.push(x);
            }
            v
        }
        3 => {
            // max size 100
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        4 => {
            // all 1s
            let n = rng.gen_range_usize(1, 100);
            vec![1; n]
        }
        5 => {
            // all 1000s
            let n = rng.gen_range_usize(1, 100);
            vec![1000; n]
        }
        6 => {
            // alternating even/odd
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 2 } else { 3 });
            }
            v
        }
        7 => {
            // mostly even with one odd at end
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![2; n - 1];
            v.push(3);
            v
        }
        8 => {
            // mostly odd with one even at start
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![2];
            for _ in 1..n {
                v.push(3);
            }
            v
        }
        9 => {
            // boundary values
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                let c = rng.gen_range_usize(0, 3);
                v.push(match c { 0 => 1, 1 => 2, 2 => 999, _ => 1000 });
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let _ = t;
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
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
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        // clamp just to be safe
        let mut clamped: Vec<i32> = Vec::new();
        for &x in &values {
            let y = if x < 1 { 1 } else if x > 1000 { 1000 } else { x };
            clamped.push(y);
        }
        if clamped.is_empty() {
            clamped.push(1);
        }
        if clamped.len() > 100 {
            clamped.truncate(100);
        }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}