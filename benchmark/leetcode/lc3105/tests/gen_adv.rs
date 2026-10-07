use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        values.len() > 0,
        values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
    ensures
        nums.len() > 0,
        nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
{
    let n: usize = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            0 <= pos <= n,
            nums.len() == pos,
            forall|k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < pos as int ==> 1 <= #[trigger] nums[k] <= 50,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
        decreases n - pos,
    {
        let v = values[pos];
        assert(1 <= v <= 50);
        nums.push(v);
        pos = pos + 1;
    }

    nums
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // random small
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 50));
            }
            v
        }
        1 => {
            // strictly increasing
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            let start = rng.gen_range_i32(1, 50 - n as i32 + 1).max(1);
            for i in 0..n {
                v.push(start + i as i32);
            }
            v
        }
        2 => {
            // strictly decreasing
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            let start = rng.gen_range_i32(n as i32, 50).max(n as i32);
            for i in 0..n {
                v.push(start - i as i32);
            }
            v
        }
        3 => {
            // all equal
            let n = rng.gen_range_usize(1, 50);
            let val = rng.gen_range_i32(1, 50);
            vec![val; n]
        }
        4 => {
            // length 1
            vec![rng.gen_range_i32(1, 50)]
        }
        5 => {
            // alternating high/low
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 50 });
            }
            v
        }
        6 => {
            // zigzag with small values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 2 } else { 1 });
            }
            v
        }
        7 => {
            // max length, random
            let n = 50;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 50));
            }
            v
        }
        8 => {
            // plateau with runs
            let n = rng.gen_range_usize(5, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur = rng.gen_range_i32(1, 50);
            let mut i = 0;
            while i < n {
                let run = rng.gen_range_usize(1, 4).min(n - i);
                for _ in 0..run {
                    v.push(cur);
                }
                i += run;
                cur = rng.gen_range_i32(1, 50);
            }
            v
        }
        9 => {
            // increasing then decreasing
            let n = rng.gen_range_usize(3, 50);
            let mid = n / 2;
            let mut v = Vec::with_capacity(n);
            for i in 0..mid {
                v.push((i as i32 + 1).min(50).max(1));
            }
            for i in 0..(n - mid) {
                let val = (mid as i32 - i as i32).max(1).min(50);
                v.push(val);
            }
            v
        }
        _ => {
            // tiny values 1..=3
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        // Ensure constraints are met
        let mut clean: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let v = if x < 1 { 1 } else if x > 50 { 50 } else { x };
            clean.push(v);
        }
        if clean.is_empty() {
            clean.push(1);
        }
        if clean.len() > 50 {
            clean.truncate(50);
        }
        let nums = generate_test_case(&clean);
        print_json(&nums);
    }
}