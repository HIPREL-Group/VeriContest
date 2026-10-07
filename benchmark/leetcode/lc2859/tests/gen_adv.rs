use vstd::prelude::*;

verus! {

pub fn generate_test_case(len: usize, vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= len <= 1000,
        vals.len() == len,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals@[i] <= 100000,
    ensures
        1 <= nums.len() <= 1000,
        nums.len() == len,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums@[i],
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums@[i] <= 100000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            nums.len() == i,
            vals.len() == len,
            1 <= len <= 1000,
            forall |j: int| 0 <= j < vals.len() ==> 1 <= #[trigger] vals@[j] <= 100000,
            forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums@[j] <= 100000,
        decreases len - i,
    {
        nums.push(vals[i]);
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

fn make_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(1);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(100000);
            }
        }
        3 => {
            for i in 0..n {
                v.push(((i % 100000) as i32) + 1);
            }
        }
        4 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 100000 });
            }
        }
        5 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        6 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(99990, 100000));
            }
        }
        7 => {
            for i in 0..n {
                v.push(((i * 37 + 1) % 100000 + 1) as i32);
            }
        }
        8 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 2));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
        }
    }
    v
}

fn choose_k(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => rng.gen_range_i32(0, 10),
        1 => 0,
        2 => 10,
        3 => 1,
        4 => 2,
        5 => rng.gen_range_i32(0, 10),
        6 => 5,
        7 => rng.gen_range_i32(0, 10),
        8 => rng.gen_range_i32(0, 3),
        _ => rng.gen_range_i32(0, 10),
    }
}

fn choose_n(rng: &mut Rng, mode: usize, t: usize) -> usize {
    match mode {
        0 => rng.gen_range_usize(1, 20),
        1 => 1000,
        2 => 1000,
        3 => if t % 2 == 0 { 1 } else { 1000 },
        4 => rng.gen_range_usize(2, 100),
        5 => 500,
        6 => rng.gen_range_usize(1, 50),
        7 => 1000,
        8 => rng.gen_range_usize(1, 10),
        _ => rng.gen_range_usize(1, 1000),
    }
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = choose_n(&mut rng, mode, t);
        let vals = make_vals(&mut rng, mode, n);
        let k = choose_k(&mut rng, mode);
        let nums = generate_test_case(n, &vals);
        print_json(&nums, k);
    }
}