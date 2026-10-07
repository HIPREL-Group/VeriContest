use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    target: i32,
    fillers: &Vec<i32>,
) -> (res: (i32, Vec<i32>))
    requires
        1 <= target <= 1_000_000_000,
        1 <= fillers.len() <= 100_000,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10_000,
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1.len() <= 100_000,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 10_000,
        res.0 == target,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10_000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 10_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (target, nums)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_case(rng: &mut Rng, mode: usize, t_idx: usize) -> (i32, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let target = rng.gen_range_i32(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
            (target, v)
        }
        1 => {
            // target larger than sum of all elements
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let mut sum: i64 = 0;
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 100);
                v.push(x);
                sum += x as i64;
            }
            let target = ((sum + 1).min(1_000_000_000) as i32).max(1);
            (target, v)
        }
        2 => {
            // single element
            let target = rng.gen_range_i32(1, 10_000);
            let x = rng.gen_range_i32(1, 10_000);
            (target, vec![x])
        }
        3 => {
            // answer is entire array
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            let mut sum: i64 = 0;
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 10);
                v.push(x);
                sum += x as i64;
            }
            let target = (sum as i32).max(1);
            (target, v)
        }
        4 => {
            // many small elements, target medium
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(1);
            }
            let target = rng.gen_range_i32(1, 100_000);
            (target, v)
        }
        5 => {
            // all max values
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(10_000);
            }
            let target = rng.gen_range_i32(1, 1_000_000_000);
            (target, v)
        }
        6 => {
            // answer is 1 (one element >= target)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 10_000;
            (rng.gen_range_i32(1, 10_000), v)
        }
        7 => {
            // large n, target = 10^9 - impossible
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(1);
            }
            (1_000_000_000, v)
        }
        8 => {
            // example 1
            (7, vec![2, 3, 1, 2, 4, 3])
        }
        9 => {
            // example 2 + 3
            if t_idx % 2 == 0 {
                (4, vec![1, 4, 4])
            } else {
                (11, vec![1, 1, 1, 1, 1, 1, 1, 1])
            }
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(10, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000));
            }
            let target = rng.gen_range_i32(1, 500_000);
            (target, v)
        }
    }
}

fn print_json(target: i32, nums: &[i32]) {
    print!("{{\"target\":{},\"nums\":[", target);
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (target, fillers) = make_case(&mut rng, mode, t);
        // Sanity clamp
        let target = if target < 1 { 1 } else if target > 1_000_000_000 { 1_000_000_000 } else { target };
        let mut safe_fillers: Vec<i32> = Vec::with_capacity(fillers.len());
        for x in &fillers {
            let v = if *x < 1 { 1 } else if *x > 10_000 { 10_000 } else { *x };
            safe_fillers.push(v);
        }
        if safe_fillers.is_empty() {
            safe_fillers.push(1);
        }
        if safe_fillers.len() > 100_000 {
            safe_fillers.truncate(100_000);
        }
        let (tgt, nums) = generate_test_case(target, &safe_fillers);
        print_json(tgt, &nums);
    }
}