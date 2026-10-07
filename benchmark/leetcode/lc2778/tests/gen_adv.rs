use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 50,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 50,
    ensures
        1 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < vals.len()
        invariant
            0 <= i <= vals.len(),
            nums.len() == i,
            vals.len() <= 50,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 50,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 50,
        decreases vals.len() - i,
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

fn build_vec(n: usize, rng: &mut Rng, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(1); }
        }
        1 => {
            for _ in 0..n { v.push(50); }
        }
        2 => {
            for i in 0..n { v.push(((i % 50) + 1) as i32); }
        }
        3 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 50 });
            }
        }
        4 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 50));
            }
        }
        5 => {
            // small values
            for _ in 0..n { v.push(rng.gen_range_i32(1, 3)); }
        }
        6 => {
            // large values
            for _ in 0..n { v.push(rng.gen_range_i32(45, 50)); }
        }
        7 => {
            // descending
            for i in 0..n {
                let val = 50 - ((i % 50) as i32);
                v.push(if val < 1 { 1 } else { val });
            }
        }
        8 => {
            // single element
            v.push(rng.gen_range_i32(1, 50));
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 50)); }
        }
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
    let total = 200usize;
    let modes = 10usize;

    // highly composite / edge sizes
    let edge_sizes = [1usize, 2, 3, 4, 6, 12, 24, 36, 48, 50];

    for t in 0..total {
        let mode = t % modes;
        let n = if t < edge_sizes.len() * modes {
            edge_sizes[t % edge_sizes.len()]
        } else if mode == 8 {
            1
        } else {
            rng.gen_range_usize(1, 50)
        };
        let n = if n < 1 { 1 } else if n > 50 { 50 } else { n };

        let mut vals = build_vec(n, &mut rng, mode);
        // ensure length in bounds and values in bounds
        if vals.len() == 0 { vals.push(1); }
        while vals.len() > 50 { vals.pop(); }
        for i in 0..vals.len() {
            if vals[i] < 1 { vals[i] = 1; }
            if vals[i] > 50 { vals[i] = 50; }
        }

        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}