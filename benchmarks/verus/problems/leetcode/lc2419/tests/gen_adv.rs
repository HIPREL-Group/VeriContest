use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    max_val: i32,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 100_000,
        1 <= max_val <= 1_000_000,
        fillers.len() + 1 == len,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= max_val,
    ensures
        1 <= nums.len() <= 100_000,
        forall|idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(max_val);
    let mut i: usize = 0;
    while i < fillers.len()
        invariant
            0 <= i <= fillers.len(),
            nums.len() == i + 1,
            1 <= max_val <= 1_000_000,
            nums[0] == max_val,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= max_val,
            forall|k: int| 1 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= max_val,
        decreases fillers.len() - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }

    assert(nums.len() == len);
    assert forall|idx: int| 0 <= idx < nums.len() implies 1 <= #[trigger] nums[idx] <= 1_000_000 by {
        if idx == 0 {
            assert(nums[0] == max_val);
        } else {
            assert(1 <= nums[idx] <= max_val);
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build(mode: usize, rng: &mut Rng) -> (usize, i32, Vec<i32>) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(50, 200),
        4 => rng.gen_range_usize(1000, 2000),
        5 => 100_000,
        6 => rng.gen_range_usize(10, 100),
        7 => rng.gen_range_usize(500, 1000),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(100, 500),
        _ => rng.gen_range_usize(1, 100),
    };

    let max_val: i32 = match mode {
        0 => rng.gen_range_i32(1, 1_000_000),
        1 => 1_000_000,
        2 => 1,
        3 => rng.gen_range_i32(1, 1_000_000),
        4 => (1 << rng.gen_range_usize(0, 19)).min(1_000_000),
        5 => rng.gen_range_i32(1, 1_000_000),
        6 => 1_000_000,
        7 => rng.gen_range_i32(900_000, 1_000_000),
        8 => rng.gen_range_i32(1, 10),
        9 => (1 << 19).min(1_000_000),
        _ => rng.gen_range_i32(1, 1_000_000),
    };

    let filler_len = n - 1;
    let mut fillers: Vec<i32> = Vec::with_capacity(filler_len);

    match mode {
        2 => {
            for _ in 0..filler_len {
                fillers.push(1);
            }
        }
        3 => {
            for _ in 0..filler_len {
                fillers.push(max_val);
            }
        }
        4 => {
            for i in 0..filler_len {
                if i % 2 == 0 {
                    fillers.push(max_val);
                } else {
                    fillers.push(1);
                }
            }
        }
        6 => {
            for i in 0..filler_len {
                if i < filler_len / 2 {
                    fillers.push(max_val);
                } else {
                    fillers.push(rng.gen_range_i32(1, max_val));
                }
            }
        }
        7 => {
            for _ in 0..filler_len {
                let r = rng.gen_range_usize(0, 2);
                if r == 0 {
                    fillers.push(max_val);
                } else {
                    fillers.push(rng.gen_range_i32(1, max_val));
                }
            }
        }
        _ => {
            for _ in 0..filler_len {
                fillers.push(rng.gen_range_i32(1, max_val));
            }
        }
    }

    (n, max_val, fillers)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, max_val, fillers) = build(mode, &mut rng);
        let nums = generate_test_case(n, max_val, &fillers);
        print_json(&nums);
    }
}