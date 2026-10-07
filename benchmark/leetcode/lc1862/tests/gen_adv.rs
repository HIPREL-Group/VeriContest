use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100_000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100_000,
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
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // tiny random
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range(1, 10)); }
            v
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(1, 1000);
            let x = rng.gen_range(1, 100_000);
            vec![x; n]
        }
        2 => {
            // all ones
            let n = rng.gen_range_usize(1, 1000);
            vec![1i32; n]
        }
        3 => {
            // all max
            let n = rng.gen_range_usize(1, 1000);
            vec![100_000i32; n]
        }
        4 => {
            // size 1
            vec![rng.gen_range(1, 100_000)]
        }
        5 => {
            // large n, small values
            let n = rng.gen_range_usize(10_000, 100_000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range(1, 100)); }
            v
        }
        6 => {
            // large n, mixed values
            let n = rng.gen_range_usize(10_000, 100_000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range(1, 100_000)); }
            v
        }
        7 => {
            // powers of 2
            let pows: [i32; 17] = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536];
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(pows[rng.gen_range_usize(0, 16)]); }
            v
        }
        8 => {
            // one big many small
            let n = rng.gen_range_usize(2, 1000);
            let mut v = Vec::with_capacity(n);
            v.push(100_000);
            for _ in 1..n { v.push(1); }
            v
        }
        9 => {
            // sequential
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push((i as i32) % 100_000 + 1); }
            v
        }
        _ => {
            // random medium
            let n = rng.gen_range_usize(1, 2000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range(1, 100_000)); }
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
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        // Clamp safety: ensure constraints
        let n = values.len();
        if n < 1 || n > 100_000 { continue; }
        let mut ok = true;
        for &x in &values { if x < 1 || x > 100_000 { ok = false; break; } }
        if !ok { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}