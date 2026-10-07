use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 500,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= nums.len() <= 500,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 500,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100000,
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

fn build_values_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // Random small sizes
            let n = rng.gen_range_usize(1, 10);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            // Max size, random
            let n = 500;
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
        2 => {
            // Boundary: all 1-digit (odd digits)
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 9));
            }
        }
        3 => {
            // Boundary: all 2-digit (even)
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(10, 99));
            }
        }
        4 => {
            // Boundary: all 3-digit (odd)
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(100, 999));
            }
        }
        5 => {
            // All 4-digit (even)
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1000, 9999));
            }
        }
        6 => {
            // All 5-digit (odd)
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(10000, 99999));
            }
        }
        7 => {
            // Exactly 100000 (6-digit, even) mixed
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(100000);
                } else {
                    v.push(rng.gen_range_i32(1, 99999));
                }
            }
        }
        8 => {
            // Single element
            v.push(rng.gen_range_i32(1, 100000));
        }
        9 => {
            // Edges around digit boundaries: 9, 10, 99, 100, 999, 1000, 9999, 10000, 99999, 100000
            let edges: [i32; 11] = [1, 9, 10, 99, 100, 999, 1000, 9999, 10000, 99999, 100000];
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, 10);
                v.push(edges[idx]);
            }
        }
        _ => {
            // Mixed random
            let n = rng.gen_range_usize(1, 500);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
    }
    if v.is_empty() {
        v.push(1);
    }
    // Safety clamp
    for i in 0..v.len() {
        if v[i] < 1 { v[i] = 1; }
        if v[i] > 100000 { v[i] = 100000; }
    }
    if v.len() > 500 {
        v.truncate(500);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % (modes + 1);
        let values = build_values_mode(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}