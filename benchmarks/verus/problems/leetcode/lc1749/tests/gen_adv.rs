use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> -10000 <= #[trigger] values[i] <= 10000,
    ensures
        1 <= nums@.len() <= 100000,
        forall|i: int| 0 <= i < nums@.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
        nums@.len() == values.len(),
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> -10000 <= #[trigger] values[k] <= 10000,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10000, 10000));
            }
            v
        }
        1 => {
            // single element
            vec![rng.gen_range_i32(-10000, 10000)]
        }
        2 => {
            // all positive
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10000));
            }
            v
        }
        3 => {
            // all negative
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10000, -1));
            }
            v
        }
        4 => {
            // all zeros
            let n = rng.gen_range_usize(1, 1000);
            vec![0; n]
        }
        5 => {
            // alternating max/min
            let n = rng.gen_range_usize(2, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(10000); } else { v.push(-10000); }
            }
            v
        }
        6 => {
            // large n, random
            let n = 100000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10000, 10000));
            }
            v
        }
        7 => {
            // large n, all max
            let n = 100000;
            vec![10000; n]
        }
        8 => {
            // large n, all min
            let n = 100000;
            vec![-10000; n]
        }
        9 => {
            // mid: sum shape to stress prefix
            let n = rng.gen_range_usize(10, 5000);
            let mut v = Vec::new();
            for i in 0..n {
                let sign = if (i + t) % 3 == 0 { -1 } else { 1 };
                v.push(sign * rng.gen_range_i32(0, 10000));
            }
            v
        }
        _ => {
            // boundary values mixed
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let choices = [-10000i32, -1, 0, 1, 10000];
            for _ in 0..n {
                let idx = (rng.next_u64() as usize) % choices.len();
                v.push(choices[idx]);
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
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build(mode, &mut rng, t);
        // sanity clamp
        let mut safe: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let y = if x < -10000 { -10000 } else if x > 10000 { 10000 } else { x };
            safe.push(y);
        }
        if safe.is_empty() {
            safe.push(0);
        }
        if safe.len() > 100000 {
            safe.truncate(100000);
        }
        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}