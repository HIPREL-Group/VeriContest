use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 2500,
        forall |i: int| 0 <= i < vals.len() ==> -10_000 <= (#[trigger] vals[i]) <= 10_000,
    ensures
        1 <= nums.len() <= 2500,
        forall |i: int| 0 <= i < nums.len() ==> -10_000 <= (#[trigger] nums[i]) <= 10_000,
{
    let n: usize = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == vals.len(),
            1 <= n <= 2500,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < vals.len() ==> -10_000 <= (#[trigger] vals[i]) <= 10_000,
            forall |k: int| 0 <= k < pos as int ==> (#[trigger] nums[k]) == vals[k],
        decreases n - pos,
    {
        let v = vals[pos];
        nums.push(v);
        pos = pos + 1;
    }

    proof {
        assert forall |i: int| 0 <= i < nums.len() implies -10_000 <= (#[trigger] nums[i]) <= 10_000 by {
            assert(nums[i] == vals[i]);
        }
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

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element
            vec![rng.gen_range_i32(-10_000, 10_000)]
        }
        1 => {
            // Strictly increasing (answer = n)
            let n = rng.gen_range_usize(2, 2500);
            let start: i32 = rng.gen_range_i32(-10_000, 10_000 - n as i32);
            (0..n).map(|i| start + i as i32).collect()
        }
        2 => {
            // Strictly decreasing (answer = 1)
            let n = rng.gen_range_usize(2, 2500);
            let start: i32 = rng.gen_range_i32(-10_000 + n as i32, 10_000);
            (0..n).map(|i| start - i as i32).collect()
        }
        3 => {
            // All equal (answer = 1)
            let n = rng.gen_range_usize(1, 2500);
            let v = rng.gen_range_i32(-10_000, 10_000);
            vec![v; n]
        }
        4 => {
            // Random small
            let n = rng.gen_range_usize(1, 30);
            (0..n).map(|_| rng.gen_range_i32(-10, 10)).collect()
        }
        5 => {
            // Random full range
            let n = rng.gen_range_usize(1, 2500);
            (0..n).map(|_| rng.gen_range_i32(-10_000, 10_000)).collect()
        }
        6 => {
            // Max size
            let n = 2500;
            (0..n).map(|_| rng.gen_range_i32(-10_000, 10_000)).collect()
        }
        7 => {
            // Non-decreasing with duplicates
            let n = rng.gen_range_usize(2, 500);
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            v.sort();
            v
        }
        8 => {
            // Two halves: increasing then decreasing
            let n = rng.gen_range_usize(4, 200);
            let mut res = Vec::with_capacity(n);
            for i in 0..n/2 {
                res.push(i as i32);
            }
            for i in 0..(n - n/2) {
                res.push((n/2 - i) as i32);
            }
            res
        }
        9 => {
            // Boundary values
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| if rng.next_u64() % 2 == 0 { -10_000 } else { 10_000 }).collect()
        }
        _ => {
            // Zigzag
            let n = rng.gen_range_usize(1, 300);
            (0..n).map(|i| if i % 2 == 0 { i as i32 } else { -(i as i32) }).collect()
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
        let vals = build_mode(&mut rng, mode);
        // Safety: clamp just in case
        let vals: Vec<i32> = vals.into_iter()
            .map(|x| if x < -10_000 { -10_000 } else if x > 10_000 { 10_000 } else { x })
            .collect();
        let vals = if vals.is_empty() { vec![0i32] } else if vals.len() > 2500 { vals[..2500].to_vec() } else { vals };
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}