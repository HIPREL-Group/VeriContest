use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
    ensures
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            2 <= n <= 100,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10_000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10_000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
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

fn build_vec(v: Vec<i32>) -> Vec<i32> {
    // Clamp to [1, 10000]
    let mut out = Vec::with_capacity(v.len());
    for x in v {
        let mut y = x;
        if y < 1 { y = 1; }
        if y > 10_000 { y = 10_000; }
        out.push(y);
    }
    out
}

fn make_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode % 11 {
        0 => 2,
        1 => 100,
        2 => rng.gen_range_usize(2, 10),
        _ => rng.gen_range_usize(2, 100),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode % 11 {
        0 => {
            // simple pair, alternating
            let a = rng.gen_range_i32(1, 9999);
            v.push(a);
            v.push(a + 1);
        }
        1 => {
            // Fully alternating long sequence: a, a+1, a, a+1, ...
            let a = rng.gen_range_i32(1, 9999);
            for i in 0..n {
                if i % 2 == 0 { v.push(a); } else { v.push(a + 1); }
            }
        }
        2 => {
            // All same value
            let a = rng.gen_range_i32(1, 10_000);
            for _ in 0..n { v.push(a); }
        }
        3 => {
            // Increasing sequence
            let start = rng.gen_range_i32(1, 9000);
            for i in 0..n { v.push(start + i as i32); }
        }
        4 => {
            // Random with many duplicates
            for _ in 0..n { v.push(rng.gen_range_i32(1, 3)); }
        }
        5 => {
            // Alternating but broken somewhere
            let a = rng.gen_range_i32(2, 9998);
            for i in 0..n {
                if i % 2 == 0 { v.push(a); } else { v.push(a + 1); }
            }
            if n >= 3 {
                let idx = rng.gen_range_usize(1, n - 1);
                v[idx] = rng.gen_range_i32(1, 10_000);
            }
        }
        6 => {
            // Two alternating segments joined
            let a = rng.gen_range_i32(1, 5000);
            let b = rng.gen_range_i32(5001, 9999);
            let mid = n / 2;
            for i in 0..mid {
                if i % 2 == 0 { v.push(a); } else { v.push(a + 1); }
            }
            for i in mid..n {
                if (i - mid) % 2 == 0 { v.push(b); } else { v.push(b + 1); }
            }
        }
        7 => {
            // Edge values 1 and 10000
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(10_000); }
            }
        }
        8 => {
            // Nearly alternating with slight decrease pattern
            let a = rng.gen_range_i32(2, 9999);
            for i in 0..n {
                if i % 2 == 0 { v.push(a); } else { v.push(a - 1); }
            }
        }
        9 => {
            // Fully random
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10_000)); }
        }
        _ => {
            // alternating with some noise
            let a = rng.gen_range_i32(1, 9999);
            for i in 0..n {
                let r = rng.next_u64() % 10;
                if r < 8 {
                    if i % 2 == 0 { v.push(a); } else { v.push(a + 1); }
                } else {
                    v.push(rng.gen_range_i32(1, 10_000));
                }
            }
        }
    }

    build_vec(v)
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    for t in 0..200 {
        let mode = t % 11;
        let values = make_mode(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}