use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
    ensures
        1 <= nums.len() <= 10_000,
        nums.len() == values.len(),
        forall |i: int| 0 <= i < nums.len() ==> 
            i32::MIN <= #[trigger] nums[i] <= i32::MAX,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n: usize = values.len();

    while i < n
        invariant
            n == values.len(),
            1 <= n <= 10_000,
            0 <= i <= n,
            nums.len() == i,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }

    assert(forall |k: int| 0 <= k < nums.len() ==>
        i32::MIN <= #[trigger] nums[k] <= i32::MAX);

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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn make_values(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // no zeros
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
        }
        2 => {
            // all zeros except one at end
            for _ in 0..n.saturating_sub(1) { v.push(0); }
            if n > 0 { v.push(rng.gen_range_i32(1, 100)); }
        }
        3 => {
            // all zeros except one at start
            if n > 0 { v.push(rng.gen_range_i32(1, 100)); }
            for _ in 1..n { v.push(0); }
        }
        4 => {
            // alternating zero / non-zero
            for i in 0..n {
                if i % 2 == 0 { v.push(0); } else { v.push(rng.gen_range_i32(1, 1000)); }
            }
        }
        5 => {
            // alternating non-zero / zero
            for i in 0..n {
                if i % 2 == 0 { v.push(rng.gen_range_i32(1, 1000)); } else { v.push(0); }
            }
        }
        6 => {
            // extremes
            for _ in 0..n {
                let r = rng.next_u64() % 4;
                let val = match r {
                    0 => i32::MIN,
                    1 => i32::MAX,
                    2 => 0,
                    _ => rng.gen_range_i32(-1000, 1000),
                };
                v.push(val);
            }
        }
        7 => {
            // negative and zeros
            for _ in 0..n {
                let r = rng.next_u64() % 3;
                if r == 0 { v.push(0); } else { v.push(rng.gen_range_i32(-1_000_000, -1)); }
            }
        }
        8 => {
            // single element
            v.push(rng.gen_range_i32(i32::MIN, i32::MAX));
        }
        9 => {
            // mostly zeros, few non-zeros scattered
            for i in 0..n {
                if i % 17 == 3 { v.push(rng.gen_range_i32(1, 1000)); } else { v.push(0); }
            }
        }
        _ => {
            // random
            for _ in 0..n {
                let r = rng.next_u64() % 5;
                if r == 0 { v.push(0); } else { v.push(rng.gen_range_i32(-10000, 10000)); }
            }
        }
    }
    v
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
        let n: usize = match mode {
            0 => 1 + (t % 10),
            1 => 2 + (t % 50),
            2 => 10,
            3 => 10,
            4 => 20,
            5 => 21,
            6 => if t % 2 == 0 { 10_000 } else { 1 },
            7 => 100,
            8 => 1,
            9 => 500,
            _ => {
                let r = (rng.next_u64() as usize) % 10_000;
                1 + r
            }
        };
        let n = if n < 1 { 1 } else if n > 10_000 { 10_000 } else { n };
        let values = make_values(&mut rng, n, mode);
        let values = if values.len() < 1 {
            let mut vv = Vec::new();
            vv.push(0);
            vv
        } else if values.len() > 10_000 {
            let mut vv = Vec::new();
            for i in 0..10_000 { vv.push(values[i]); }
            vv
        } else {
            values
        };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}