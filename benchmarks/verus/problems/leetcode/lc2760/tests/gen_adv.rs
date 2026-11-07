use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    threshold: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 100,
        1 <= threshold <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.1 <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] (result.0)[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    (nums, threshold)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, i32) {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all even small
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50));
            }
            let t = rng.gen_range_i32(1, 100);
            (v, t)
        }
        1 => {
            // all odd
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50) - 1);
            }
            let t = rng.gen_range_i32(1, 100);
            (v, t)
        }
        2 => {
            // strict alternating even/odd starting even
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(2 * rng.gen_range_i32(1, 50));
                } else {
                    v.push(2 * rng.gen_range_i32(1, 50) - 1);
                }
            }
            (v, rng.gen_range_i32(1, 100))
        }
        3 => {
            // strict alternating odd/even starting odd
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(2 * rng.gen_range_i32(1, 50) - 1);
                } else {
                    v.push(2 * rng.gen_range_i32(1, 50));
                }
            }
            (v, rng.gen_range_i32(1, 100))
        }
        4 => {
            // all values equal to threshold
            let t = rng.gen_range_i32(1, 100);
            for _ in 0..n {
                v.push(t);
            }
            (v, t)
        }
        5 => {
            // values above threshold mostly
            let t = rng.gen_range_i32(1, 50);
            for _ in 0..n {
                v.push(rng.gen_range_i32(t + 1, 100).max(1));
            }
            (v, t)
        }
        6 => {
            // examples-like: insert a good alternating subarray
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (v, rng.gen_range_i32(1, 100))
        }
        7 => {
            // threshold = 1 edge
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (v, 1)
        }
        8 => {
            // threshold = 100 (no threshold effect)
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (v, 100)
        }
        9 => {
            // small values 1..=2
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 2));
            }
            (v, rng.gen_range_i32(1, 100))
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (v, rng.gen_range_i32(1, 100))
        }
    }
}

fn print_json(nums: &[i32], threshold: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"threshold\":{}}}", threshold);
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

    // Specific examples first
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![3,2,5,4], 5),
        (vec![1,2], 2),
        (vec![2,3,4,5], 4),
        (vec![1], 1),
        (vec![2], 2),
        (vec![100], 100),
        (vec![1], 100),
        (vec![100], 1),
    ];
    for (nums, t) in examples.iter() {
        let (out_nums, out_t) = generate_test_case(nums, *t);
        print_json(&out_nums, out_t);
    }

    for k in 0..total {
        let mode = k % modes;
        let n = rng.gen_range_usize(1, 100);
        let (values, t) = build_values(&mut rng, mode, n);
        let (out_nums, out_t) = generate_test_case(&values, t);
        print_json(&out_nums, out_t);
    }
}