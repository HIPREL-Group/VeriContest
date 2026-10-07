use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    nums_raw: &Vec<i32>,
    pattern_raw: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= n <= 100,
        1 <= m < n,
        nums_raw.len() == n,
        pattern_raw.len() == m,
        forall |i: int| 0 <= i < nums_raw.len() ==> 1 <= #[trigger] nums_raw[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < pattern_raw.len() ==> -1 <= #[trigger] pattern_raw[i] <= 1,
    ensures
        2 <= result.0.len() <= 100,
        1 <= result.1.len() < result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < result.1.len() ==> -1 <= #[trigger] result.1[i] <= 1,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_raw.len()
        invariant
            0 <= i <= nums_raw.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == nums_raw[k],
            forall |k: int| 0 <= k < nums_raw.len() ==> 1 <= #[trigger] nums_raw[k] <= 1_000_000_000,
        decreases nums_raw.len() - i,
    {
        nums.push(nums_raw[i]);
        i = i + 1;
    }

    let mut pattern: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < pattern_raw.len()
        invariant
            0 <= j <= pattern_raw.len(),
            pattern.len() == j,
            forall |k: int| 0 <= k < j as int ==> #[trigger] pattern[k] == pattern_raw[k],
            forall |k: int| 0 <= k < pattern_raw.len() ==> -1 <= #[trigger] pattern_raw[k] <= 1,
        decreases pattern_raw.len() - j,
    {
        pattern.push(pattern_raw[j]);
        j = j + 1;
    }

    (nums, pattern)
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
        lo + v as i32
    }
}

fn mode_nums_pattern(rng: &mut Rng, mode: usize, n: usize, m: usize) -> (Vec<i32>, Vec<i32>) {
    let mut nums: Vec<i32> = Vec::with_capacity(n);
    let mut pattern: Vec<i32> = Vec::with_capacity(m);

    match mode {
        0 => {
            // strictly increasing
            for i in 0..n {
                nums.push((i as i32) + 1);
            }
            for _ in 0..m {
                pattern.push(1);
            }
        }
        1 => {
            // strictly decreasing
            for i in 0..n {
                nums.push((n as i32) - (i as i32));
            }
            for _ in 0..m {
                pattern.push(-1);
            }
        }
        2 => {
            // all equal
            let v = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n {
                nums.push(v);
            }
            for _ in 0..m {
                pattern.push(0);
            }
        }
        3 => {
            // zig-zag 1,2,1,2
            for i in 0..n {
                nums.push(if i % 2 == 0 { 1 } else { 2 });
            }
            for i in 0..m {
                pattern.push(if i % 2 == 0 { 1 } else { -1 });
            }
        }
        4 => {
            // random small values
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 5));
            }
            for _ in 0..m {
                pattern.push(rng.gen_range_i32(-1, 1));
            }
        }
        5 => {
            // random large values
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            for _ in 0..m {
                pattern.push(rng.gen_range_i32(-1, 1));
            }
        }
        6 => {
            // pattern all zeros with variable nums
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 10));
            }
            for _ in 0..m {
                pattern.push(0);
            }
        }
        7 => {
            // boundary: max values
            for i in 0..n {
                let v = 1_000_000_000 - (i as i32);
                nums.push(if v < 1 { 1 } else { v });
            }
            for _ in 0..m {
                pattern.push(-1);
            }
        }
        8 => {
            // alternating pattern values -1,0,1
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 20));
            }
            for i in 0..m {
                let p: i32 = ((i % 3) as i32) - 1;
                pattern.push(p);
            }
        }
        9 => {
            // nums like 1,1,2,2,1,1,... pattern could be 0,1,0,-1
            for i in 0..n {
                let block = i / 2;
                nums.push(((block % 5) as i32) + 1);
            }
            for i in 0..m {
                pattern.push(((i as i32) % 3) - 1);
            }
        }
        _ => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 100));
            }
            for _ in 0..m {
                pattern.push(rng.gen_range_i32(-1, 1));
            }
        }
    }

    (nums, pattern)
}

fn print_json(nums: &[i32], pattern: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"pattern\":[");
    for i in 0..pattern.len() {
        if i > 0 { print!(","); }
        print!("{}", pattern[i]);
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
        // choose n in [2,100], m in [1,n-1]
        let n: usize = match t % 7 {
            0 => 2,
            1 => 3,
            2 => 100,
            3 => 99,
            4 => rng.gen_range_usize(2, 100),
            5 => rng.gen_range_usize(10, 50),
            _ => rng.gen_range_usize(2, 100),
        };
        let m: usize = if n == 2 {
            1
        } else {
            match t % 5 {
                0 => 1,
                1 => n - 1,
                2 => n / 2,
                _ => rng.gen_range_usize(1, n - 1),
            }
        };

        let (nums_raw, pattern_raw) = mode_nums_pattern(&mut rng, mode, n, m);

        // sanity-clamp (in case any element fell out of range)
        let mut nums_raw = nums_raw;
        for i in 0..nums_raw.len() {
            if nums_raw[i] < 1 { nums_raw[i] = 1; }
            if nums_raw[i] > 1_000_000_000 { nums_raw[i] = 1_000_000_000; }
        }
        let mut pattern_raw = pattern_raw;
        for i in 0..pattern_raw.len() {
            if pattern_raw[i] < -1 { pattern_raw[i] = -1; }
            if pattern_raw[i] > 1 { pattern_raw[i] = 1; }
        }

        let (nums, pattern) = generate_test_case(n, m, &nums_raw, &pattern_raw);
        print_json(&nums, &pattern);
    }
}