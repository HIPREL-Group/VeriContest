use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    nums
}

}

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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 1_000_000_000 { 1_000_000_000 } else { v }
}

fn build(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // all distinct
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) + 1);
            }
            v
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_i32(1, 1_000_000_000);
            vec![x; n]
        }
        2 => {
            // single element
            vec![rng.gen_range_i32(1, 1_000_000_000)]
        }
        3 => {
            // large N, all distinct
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) + 1);
            }
            v
        }
        4 => {
            // large N, all same
            vec![42; 100_000]
        }
        5 => {
            // pattern like [1,2,1,3]
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(((i % 3) as i32) + 1);
            }
            v
        }
        6 => {
            // two blocks forced
            let n = rng.gen_range_usize(4, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i == 0 || i == n/2 { v.push(7); }
                else { v.push(((i as i32) % 100) + 10); }
            }
            v
        }
        7 => {
            // boundaries: first equals last
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            v.push(5);
            for i in 1..n-1 {
                v.push(rng.gen_range_i32(10, 100));
            }
            v.push(5);
            v
        }
        8 => {
            // small values, random
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
            v
        }
        9 => {
            // max values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(999_999_990, 1_000_000_000));
            }
            v
        }
        10 => {
            // interleaving pairs
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(((i % 5) as i32) + 1);
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let maxv = rng.gen_range_i32(1, 20);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, maxv));
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

    let total = 200usize;
    let modes = 12usize;

    for t in 0..total {
        let mode = if t < modes * 2 { t % modes } else { (rng.next_u64() as usize) % (modes + 1) };
        let raw = build(mode, &mut rng, t);
        let cleaned: Vec<i32> = raw.iter().map(|&x| clamp_val(x)).collect();
        let bounded: Vec<i32> = if cleaned.len() > 100_000 {
            cleaned[..100_000].to_vec()
        } else if cleaned.is_empty() {
            vec![1]
        } else {
            cleaned
        };
        let nums = generate_test_case(&bounded);
        print_json(&nums);
    }
}