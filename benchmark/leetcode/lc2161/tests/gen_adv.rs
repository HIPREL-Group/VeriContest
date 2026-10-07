use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    pivot: i32,
    pivot_idx: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        -1_000_000 <= pivot <= 1_000_000,
        fillers.len() + 1 >= 1,
        fillers.len() + 1 <= 100_000,
        pivot_idx < fillers.len() + 1,
        forall|i: int| 0 <= i < fillers.len() ==>
            -1_000_000 <= #[trigger] fillers[i] <= 1_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000 <= #[trigger] nums[i] <= 1_000_000,
        exists|i: int| 0 <= i < nums.len() && nums[i] == pivot,
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(pivot);
    proof {
        assert(exists|i: int| 0 <= i < nums.len() && nums[i] == pivot) by {
            assert(0 <= 0 < nums.len() && nums[0] == pivot);
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
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn make_fillers(rng: &mut Rng, count: usize, mode: usize, pivot: i32) -> Vec<i32> {
    let mut res: Vec<i32> = Vec::with_capacity(count);
    for i in 0..count {
        let v: i32 = match mode {
            0 => rng.gen_range_i64(-1_000_000, 1_000_000) as i32,
            1 => {
                // all less than pivot
                let lo = -1_000_000i64;
                let hi = (pivot as i64) - 1;
                if hi < lo { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
            }
            2 => {
                // all greater than pivot
                let lo = (pivot as i64) + 1;
                let hi = 1_000_000i64;
                if lo > hi { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
            }
            3 => pivot, // all equal to pivot
            4 => {
                // alternating less/greater
                if i % 2 == 0 {
                    let lo = -1_000_000i64;
                    let hi = (pivot as i64) - 1;
                    if hi < lo { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                } else {
                    let lo = (pivot as i64) + 1;
                    let hi = 1_000_000i64;
                    if lo > hi { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                }
            }
            5 => {
                // sorted-like: less first, then greater
                if i < count / 2 {
                    let lo = -1_000_000i64;
                    let hi = (pivot as i64) - 1;
                    if hi < lo { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                } else {
                    let lo = (pivot as i64) + 1;
                    let hi = 1_000_000i64;
                    if lo > hi { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                }
            }
            6 => {
                // reverse-sorted-like
                if i < count / 2 {
                    let lo = (pivot as i64) + 1;
                    let hi = 1_000_000i64;
                    if lo > hi { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                } else {
                    let lo = -1_000_000i64;
                    let hi = (pivot as i64) - 1;
                    if hi < lo { pivot } else { rng.gen_range_i64(lo, hi) as i32 }
                }
            }
            7 => {
                // extremes
                let pick = rng.gen_range_usize(0, 2);
                match pick {
                    0 => -1_000_000i32,
                    1 => 1_000_000i32,
                    _ => pivot,
                }
            }
            8 => {
                // many equal to pivot
                if i % 3 == 0 { pivot } else { rng.gen_range_i64(-1_000_000, 1_000_000) as i32 }
            }
            9 => {
                // small range around pivot
                let lo = (pivot as i64 - 3).max(-1_000_000);
                let hi = (pivot as i64 + 3).min(1_000_000);
                rng.gen_range_i64(lo, hi) as i32
            }
            _ => rng.gen_range_i64(-1_000_000, 1_000_000) as i32,
        };
        // clamp
        let v = v.max(-1_000_000).min(1_000_000);
        res.push(v);
    }
    res
}

fn print_json(nums: &[i32], pivot: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"pivot\":{}}}", pivot);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1 + (t % 8),
            1 => 2 + (t % 16),
            2 => 50,
            3 => if t % 2 == 0 { 1 } else { 100 },
            4 => 100,
            5 => 500,
            6 => 500,
            7 => if t % 3 == 0 { 100_000 } else { 1_000 },
            8 => 333,
            9 => 64,
            _ => 17,
        };
        let n = n.max(1).min(100_000);

        let pivot: i32 = match mode {
            3 => rng.gen_range_i64(-1_000_000, 1_000_000) as i32,
            7 => {
                let p = rng.gen_range_usize(0, 2);
                match p {
                    0 => -1_000_000,
                    1 => 1_000_000,
                    _ => 0,
                }
            }
            _ => rng.gen_range_i64(-1_000_000, 1_000_000) as i32,
        };

        let pivot_idx = rng.gen_range_usize(0, n - 1);
        let fillers = make_fillers(&mut rng, n - 1, mode, pivot);

        let nums = generate_test_case(pivot, pivot_idx, &fillers);
        print_json(&nums, pivot);
    }
}
