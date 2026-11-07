use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= fillers.len() <= 500_000,
    ensures
        1 <= nums.len() <= 500_000,
        nums.len() == fillers.len(),
        forall|i: int| 0 <= i < nums.len() ==> nums[i] == fillers[i],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n: usize = fillers.len();
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
        decreases n - i,
    {
        nums.push(fillers[i]);
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // tiny increasing
            let n = 1 + (t % 10);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(i as i32);
            }
            v
        }
        1 => {
            // tiny decreasing
            let n = 1 + (t % 10);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((n - i) as i32);
            }
            v
        }
        2 => {
            // the tricky one from example 3
            vec![2, 1, 5, 0, 4, 6]
        }
        3 => {
            // all same
            let n = 1 + (t % 100);
            let val = rng.gen_range_i32(-1000, 1000);
            vec![val; n]
        }
        4 => {
            // random small
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
        5 => {
            // big increasing
            let n = rng.gen_range_usize(1000, 10000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(i as i32 - (n / 2) as i32);
            }
            v
        }
        6 => {
            // big decreasing (no triplet)
            let n = rng.gen_range_usize(1000, 10000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((n - i) as i32);
            }
            v
        }
        7 => {
            // extremes
            let n = rng.gen_range_usize(3, 20);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(i32::MAX);
                } else {
                    v.push(i32::MIN);
                }
            }
            v
        }
        8 => {
            // two small followed by large sequence e.g. near-miss
            // pattern: a, small, b where b > a but between interspersed
            let n = rng.gen_range_usize(3, 30);
            let mut v = Vec::with_capacity(n);
            // descending then one big
            for i in 0..(n-1) {
                v.push((n - i) as i32);
            }
            v.push(i32::MAX);
            v
        }
        9 => {
            // zigzag
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push((i as i32) * 2);
                } else {
                    v.push(-(i as i32));
                }
            }
            v
        }
        _ => {
            // random mid
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000, 1_000_000));
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
        let mut fillers = gen_mode(&mut rng, mode, t);
        if fillers.is_empty() {
            fillers.push(0);
        }
        if fillers.len() > 500_000 {
            fillers.truncate(500_000);
        }
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}