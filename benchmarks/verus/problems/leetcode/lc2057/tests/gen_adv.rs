use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 9,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 9,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 9,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 9,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // len 1, single digit
            let v = rng.gen_i32(0, 9);
            vec![v]
        }
        1 => {
            // all zeros - index 0 always matches
            let n = rng.gen_usize(1, 100);
            vec![0i32; n]
        }
        2 => {
            // no match anywhere: nums[i] = (i%10 + 1) % 10
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((i % 10) as i32 + 1) % 10);
            }
            v
        }
        3 => {
            // all nines
            let n = rng.gen_usize(1, 100);
            vec![9i32; n]
        }
        4 => {
            // exact identity: nums[i] = i%10 -> match at 0
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i % 10) as i32);
            }
            v
        }
        5 => {
            // match only at last index
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i == n - 1 {
                    v.push((i % 10) as i32);
                } else {
                    v.push(((i % 10) as i32 + 1) % 10);
                }
            }
            v
        }
        6 => {
            // match only at single random index
            let n = rng.gen_usize(1, 100);
            let m = rng.gen_usize(0, n - 1);
            let mut v = Vec::new();
            for i in 0..n {
                if i == m {
                    v.push((i % 10) as i32);
                } else {
                    v.push(((i % 10) as i32 + 1) % 10);
                }
            }
            v
        }
        7 => {
            // random digits
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_i32(0, 9));
            }
            v
        }
        8 => {
            // len 100, random
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_i32(0, 9));
            }
            v
        }
        9 => {
            // len > 10 to test mod 10
            let n = rng.gen_usize(11, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i >= 10 && i < 20 {
                    v.push((i % 10) as i32);
                } else {
                    v.push(((i % 10) as i32 + 3) % 10);
                }
            }
            v
        }
        _ => {
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_i32(0, 9));
            }
            let _ = t;
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode, t);
        // safety: ensure constraints
        let mut safe = values.clone();
        if safe.is_empty() {
            safe.push(0);
        }
        if safe.len() > 100 {
            safe.truncate(100);
        }
        for x in safe.iter_mut() {
            if *x < 0 { *x = 0; }
            if *x > 9 { *x = 9; }
        }
        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}