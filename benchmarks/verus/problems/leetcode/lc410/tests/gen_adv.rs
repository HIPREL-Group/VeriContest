use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k_val: i32,
    max_sum_val: i64,
) -> (result: (Vec<i32>, i32, i64))
    requires
        1 <= values.len() <= 1_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000,
        1 <= k_val <= 50,
        k_val as int <= values.len() as int,
        0 <= max_sum_val <= 1_000_000_000i64,
    ensures
        ({
            let (nums, k, max_sum) = result;
            &&& 1 <= nums.len() <= 1_000
            &&& forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000
            &&& 1 <= k <= 50
            &&& k as int <= nums.len() as int
            &&& 0 <= max_sum <= 1_000_000_000i64
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 1_000_000,
            forall|j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 1_000_000,
        decreases values.len() - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    (nums, k_val, max_sum_val)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i64)
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i64) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
        1 => {
            // k == n
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = n as i32;
            (v, k, 1_000_000_000)
        }
        2 => {
            // k == 1
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            (v, 1, 1_000_000_000)
        }
        3 => {
            // all zeros
            let n = rng.gen_range_usize(1, 1000);
            let v = vec![0i32; n];
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 10);
            (v, k as i32, ms)
        }
        4 => {
            // all max
            let n = rng.gen_range_usize(1, 1000);
            let v = vec![1_000_000i32; n];
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
        5 => {
            // large random full size
            let n = 1000;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = rng.gen_range_usize(1, 50);
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
        6 => {
            // max_sum = 0
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            let k = rng.gen_range_usize(1, n.min(50));
            (v, k as i32, 0)
        }
        7 => {
            // one big element
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![0i32; n];
            v[rng.gen_range_usize(0, n - 1)] = 1_000_000;
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
        8 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i * 2000) as i32);
            }
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
        9 => {
            // boundary sum matches exactly
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            let mut total: i64 = 0;
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 100);
                v.push(x);
                total += x as i64;
            }
            let k = rng.gen_range_usize(1, n.min(50));
            (v, k as i32, total)
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let k = rng.gen_range_usize(1, n.min(50));
            let ms = rng.gen_range_i64(0, 1_000_000_000);
            (v, k as i32, ms)
        }
    }
}

fn print_json(nums: &[i32], k: i32, max_sum: i64) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{},\"max_sum\":{}}}", k, max_sum);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (values, k, max_sum) = build_case(&mut rng, mode);
        // Ensure constraints held before calling generator
        if values.is_empty() || values.len() > 1000 { continue; }
        if k < 1 || k > 50 || (k as usize) > values.len() { continue; }
        if max_sum < 0 || max_sum > 1_000_000_000 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 0 || x > 1_000_000 { ok = false; break; }
        }
        if !ok { continue; }
        let (nums, kk, ms) = generate_test_case(&values, k, max_sum);
        print_json(&nums, kk, ms);
    }
}