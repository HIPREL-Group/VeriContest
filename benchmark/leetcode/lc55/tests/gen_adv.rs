use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100_000,
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

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_range_i32(0, 100_000)]
        }
        1 => {
            // all zeros (unreachable except len 1)
            let n = rng.gen_range_usize(2, 20);
            vec![0i32; n]
        }
        2 => {
            // all ones - reachable
            let n = rng.gen_range_usize(2, 100);
            vec![1i32; n]
        }
        3 => {
            // zero in the middle blocking
            let n = rng.gen_range_usize(5, 50);
            let mut v = Vec::new();
            for i in 0..n {
                if i == n/2 { v.push(0); }
                else { v.push(rng.gen_range_i32(1, 3)); }
            }
            v
        }
        4 => {
            // large first jump covers everything
            let n = rng.gen_range_usize(2, 1000);
            let mut v = vec![n as i32; 1];
            for _ in 1..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        5 => {
            // max length
            let n = 10_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 3));
            }
            v
        }
        6 => {
            // decreasing sequence: [n, n-1, ..., 1, 0] - reachable
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((n - i) as i32 - 1);
            }
            v
        }
        7 => {
            // example 2: [3,2,1,0,4]
            vec![3, 2, 1, 0, 4]
        }
        8 => {
            // barely-reachable: each exactly reaches next
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![1i32; n];
            v[n-1] = 0;
            v
        }
        9 => {
            // large values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100_000));
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            let _ = t;
            v
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode, t);
        // clamp
        let mut clamped: Vec<i32> = Vec::new();
        for &x in &values {
            let y = if x < 0 { 0 } else if x > 100_000 { 100_000 } else { x };
            clamped.push(y);
        }
        if clamped.is_empty() { clamped.push(0); }
        if clamped.len() > 10_000 { clamped.truncate(10_000); }
        let nums = generate_test_case(&clamped);
        print_json(&nums);
    }
}