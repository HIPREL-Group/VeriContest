use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= fillers.len() <= 100,
        forall |i: int| 0 <= i < fillers.len() ==> -100 <= #[trigger] fillers[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let n = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> -100 <= #[trigger] fillers[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> -100 <= #[trigger] nums[k] <= 100,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_fillers(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all positive small, contiguous starting from 1
            for i in 0..n {
                v.push((i as i32) + 1);
            }
        }
        1 => {
            // all negative
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, -1));
            }
        }
        2 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        3 => {
            // all 100
            for _ in 0..n {
                v.push(100);
            }
        }
        4 => {
            // all -100
            for _ in 0..n {
                v.push(-100);
            }
        }
        5 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
        6 => {
            // 1..=n shuffled-ish with missing one
            let skip = rng.gen_range_usize(1, n.max(1));
            for i in 0..n {
                let val = if (i + 1) == skip { (n as i32) + 1 } else { (i as i32) + 1 };
                v.push(val.min(100));
            }
        }
        7 => {
            // mostly 1s
            for _ in 0..n {
                if rng.next_u64() % 4 == 0 {
                    v.push(rng.gen_range_i32(-100, 100));
                } else {
                    v.push(1);
                }
            }
        }
        8 => {
            // positives only 1..=100 random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        9 => {
            // one big positive dominating, rest negative
            v.push(100);
            for _ in 1..n {
                v.push(rng.gen_range_i32(-100, 0));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    // Clamp to [-100,100] just in case
    for x in v.iter_mut() {
        if *x < -100 { *x = -100; }
        if *x > 100 { *x = 100; }
    }
    // Ensure length constraints
    while v.len() > 100 {
        v.pop();
    }
    if v.is_empty() {
        v.push(0);
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n_raw = match mode {
            0 => 1 + (t % 10),
            1 => 2 + (t % 20),
            2 => 1 + (t % 100),
            3 => 100,
            4 => 100,
            5 => 1 + (rng.next_u64() as usize % 100),
            6 => 3 + (t % 50),
            7 => 5 + (t % 90),
            8 => 1 + (t % 100),
            9 => 2 + (t % 50),
            _ => 1 + (t % 100),
        };
        let n = if n_raw < 1 { 1 } else if n_raw > 100 { 100 } else { n_raw };

        let fillers = make_fillers(&mut rng, mode, n);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}