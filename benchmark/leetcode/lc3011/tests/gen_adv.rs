use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 256,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 256,
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
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 256,
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn popcount(mut x: i32) -> u32 {
    let mut c = 0;
    while x > 0 {
        c += (x & 1) as u32;
        x >>= 1;
    }
    c
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 100,
        3 => rng.gen_range_usize(1, 100),
        4 => rng.gen_range_usize(1, 10),
        5 => 100,
        6 => rng.gen_range_usize(50, 100),
        7 => 100,
        8 => rng.gen_range_usize(1, 100),
        9 => rng.gen_range_usize(2, 100),
        _ => rng.gen_range_usize(1, 100),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { v.push(rng.gen_range(1, 256)); }
        1 => {
            v.push(rng.gen_range(1, 256));
            v.push(rng.gen_range(1, 256));
        }
        2 => {
            // sorted ascending
            for _ in 0..n { v.push(rng.gen_range(1, 256)); }
            v.sort();
        }
        3 => {
            // already sorted
            for _ in 0..n { v.push(rng.gen_range(1, 256)); }
            v.sort();
        }
        4 => {
            // strictly decreasing
            for _ in 0..n { v.push(rng.gen_range(1, 256)); }
            v.sort();
            v.reverse();
        }
        5 => {
            // all same popcount (powers of 2)
            let pows: [i32; 9] = [1, 2, 4, 8, 16, 32, 64, 128, 256];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, 8);
                v.push(pows[idx]);
            }
        }
        6 => {
            // mix of single-bit and multi-bit
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    let pows: [i32; 9] = [1, 2, 4, 8, 16, 32, 64, 128, 256];
                    let idx = rng.gen_range_usize(0, 8);
                    v.push(pows[idx]);
                } else {
                    v.push(rng.gen_range(1, 256));
                }
            }
        }
        7 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        8 => {
            // boundary values
            for _ in 0..n {
                let choice = rng.gen_range_usize(0, 4);
                let val = match choice {
                    0 => 1,
                    1 => 256,
                    2 => 255,
                    3 => 128,
                    _ => rng.gen_range(1, 256),
                };
                v.push(val);
            }
        }
        9 => {
            // group by popcount, shuffled within
            for _ in 0..n { v.push(rng.gen_range(1, 256)); }
            // sort by popcount
            v.sort_by_key(|&x| popcount(x));
            // within each popcount group, randomize a bit
            let len = v.len();
            for _ in 0..len {
                let i = rng.gen_range_usize(0, len - 1);
                let j = rng.gen_range_usize(0, len - 1);
                if popcount(v[i]) == popcount(v[j]) {
                    v.swap(i, j);
                }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range(1, 256)); }
        }
    }

    // Apply adversarial patterns
    if t % 7 == 3 && v.len() >= 2 {
        // swap first two
        v.swap(0, 1);
    }

    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode, t);
        // safeguard constraints
        let mut safe: Vec<i32> = Vec::new();
        for &x in &values {
            let v = if x < 1 { 1 } else if x > 256 { 256 } else { x };
            safe.push(v);
            if safe.len() >= 100 { break; }
        }
        if safe.is_empty() { safe.push(1); }
        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}