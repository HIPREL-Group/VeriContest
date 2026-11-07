use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        values.len() >= 1,
        values.len() <= 5000,
        forall|i: int| 0 <= i < values.len() ==> -1000 <= #[trigger] values[i] <= 1000,
    ensures
        nums.len() >= 1,
        nums.len() <= 5000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            n <= 5000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> -1000 <= #[trigger] values[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> -1000 <= #[trigger] nums[k] <= 1000,
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    v.into_iter()
        .map(|x| if x < -1000 { -1000 } else if x > 1000 { 1000 } else { x })
        .collect()
}

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // length 1
            vec![rng.gen_range_i32(-1000, 1000)]
        }
        1 => {
            // length 2
            vec![rng.gen_range_i32(-1000, 1000), rng.gen_range_i32(-1000, 1000)]
        }
        2 => {
            // arithmetic sequence (all)
            let n = rng.gen_range_usize(3, 50);
            let start = rng.gen_range_i32(-500, 500);
            let d = rng.gen_range_i32(-10, 10);
            let mut v = Vec::new();
            for i in 0..n {
                let val = start as i64 + (i as i64) * (d as i64);
                v.push(val as i32);
            }
            clamp_vec(v)
        }
        3 => {
            // all equal (arithmetic with d=0)
            let n = rng.gen_range_usize(3, 100);
            let x = rng.gen_range_i32(-1000, 1000);
            vec![x; n]
        }
        4 => {
            // max length, arithmetic
            let n = 5000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let val = -1000 + ((i as i32) % 2001);
                v.push(val);
            }
            v
        }
        5 => {
            // max length, random
            let n = 5000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            v
        }
        6 => {
            // two arithmetic runs joined
            let n1 = rng.gen_range_usize(3, 20);
            let n2 = rng.gen_range_usize(3, 20);
            let mut v = Vec::new();
            let mut cur: i64 = rng.gen_range_i32(-500, 500) as i64;
            let d1 = rng.gen_range_i32(-5, 5) as i64;
            for _ in 0..n1 {
                v.push(cur as i32);
                cur += d1;
            }
            let d2 = rng.gen_range_i32(-5, 5) as i64;
            for _ in 0..n2 {
                v.push(cur as i32);
                cur += d2;
            }
            clamp_vec(v)
        }
        7 => {
            // alternating high/low (no arith slices typically)
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1000 } else { -1000 });
            }
            v
        }
        8 => {
            // short random
            let n = rng.gen_range_usize(3, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            v
        }
        9 => {
            // exactly 3 arithmetic
            let a = rng.gen_range_i32(-500, 500);
            let d = rng.gen_range_i32(-100, 100);
            vec![a, (a as i64 + d as i64) as i32, (a as i64 + 2 * d as i64) as i32]
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            v
        }
    }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = make_case(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}