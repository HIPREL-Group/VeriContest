use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    k_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 100,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
        1 <= k_val <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < vals.len()
        invariant
            0 <= i <= vals.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> #[trigger] nums[j] == vals[j],
            forall |j: int| 0 <= j < vals.len() ==> 1 <= #[trigger] vals[j] <= 100,
        decreases vals.len() - i,
    {
        nums.push(vals[i]);
        i = i + 1;
    }
    assert(nums.len() == vals.len());
    assert(forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100);
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let k = rng.gen_range_i32(1, 10);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
            (v, k)
        }
        1 => {
            // all equal
            let n = rng.gen_range_usize(2, 100);
            let val = rng.gen_range_i32(1, 100);
            let k = rng.gen_range_i32(1, 100);
            let v = vec![val; n];
            (v, k)
        }
        2 => {
            // all distinct
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for i in 0..n { v.push(((i % 100) + 1) as i32); }
            (v, k)
        }
        3 => {
            // k = 1
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
            (v, 1)
        }
        4 => {
            // k = 100
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 3)); }
            (v, 100)
        }
        5 => {
            // n = 1
            let k = rng.gen_range_i32(1, 100);
            (vec![rng.gen_range_i32(1, 100)], k)
        }
        6 => {
            // n = 100, small value range
            let k = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..100 { v.push(rng.gen_range_i32(1, 2)); }
            (v, k)
        }
        7 => {
            // two values alternating
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_i32(1, 20);
            let mut v = Vec::new();
            for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 2 }); }
            (v, k)
        }
        8 => {
            // index 0 involved (i*j = 0)
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_i32(2, 100);
            let mut v = Vec::new();
            let val = rng.gen_range_i32(1, 100);
            v.push(val);
            for _ in 1..n { v.push(val); }
            (v, k)
        }
        9 => {
            // k prime large
            let n = rng.gen_range_usize(1, 100);
            let k = 97;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, k)
        }
    }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (vals, k) = build_mode(&mut rng, mode);
        let (nums, k_out) = generate_test_case(&vals, k);
        print_json(&nums, k_out);
    }
}