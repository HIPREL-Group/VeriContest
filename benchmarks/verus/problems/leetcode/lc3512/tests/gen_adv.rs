use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    k_val: i32,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= len <= 1000,
        vals.len() == len,
        1 <= k_val <= 100,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            nums.len() == i,
            vals.len() == len,
            forall|j: int| 0 <= j < vals.len() ==> 1 <= #[trigger] vals[j] <= 1000,
            forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 1000,
        decreases len - i,
    {
        nums.push(vals[i]);
        i = i + 1;
    }
    (nums, k_val)
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<i32>) {
    let (len, k_val) = match mode {
        0 => (1usize, rng.range_i32(1, 100)),
        1 => (1000usize, rng.range_i32(1, 100)),
        2 => (rng.range_usize(1, 10), 1i32),
        3 => (rng.range_usize(1, 100), 100i32),
        4 => (rng.range_usize(1, 1000), rng.range_i32(1, 100)),
        5 => {
            let n = rng.range_usize(1, 50);
            (n, rng.range_i32(1, 100))
        }
        6 => (500usize, 7i32),
        7 => (rng.range_usize(2, 20), rng.range_i32(1, 10)),
        8 => (1000usize, 1i32),
        9 => (1000usize, 100i32),
        _ => (rng.range_usize(1, 200) + t % 50, rng.range_i32(1, 100)),
    };

    let mut vals: Vec<i32> = Vec::with_capacity(len);
    match mode {
        0 => { vals.push(rng.range_i32(1, 1000)); }
        1 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        2 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        3 => {
            for _ in 0..len {
                vals.push(1000i32);
            }
        }
        4 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        5 => {
            for _ in 0..len {
                vals.push(1i32);
            }
        }
        6 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        7 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 5));
            }
        }
        8 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        9 => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
        _ => {
            for _ in 0..len {
                vals.push(rng.range_i32(1, 1000));
            }
        }
    }
    (len, k_val, vals)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (len, k_val, vals) = build_case(&mut rng, mode, t);
        let (nums, k) = generate_test_case(len, k_val, &vals);
        print_json(&nums, k);
    }
}