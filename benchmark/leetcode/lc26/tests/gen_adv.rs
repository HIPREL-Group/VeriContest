use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: i32, increments: &Vec<u8>) -> (nums: Vec<i32>)
    requires
        -100 <= base <= 100,
        1 <= increments.len() <= 30_000,
        forall |i: int| 0 <= i < increments.len() ==> #[trigger] increments[i] <= 1u8,
    ensures
        1 <= nums.len() <= 30_000,
        nums.len() == increments.len(),
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
        forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
{
    let n = increments.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut cur: i32 = base;
    let mut k: usize = 0;

    while k < n
        invariant
            n == increments.len(),
            0 <= k <= n,
            nums.len() == k,
            -100 <= cur <= 100,
            -100 <= base <= 100,
            base <= cur,
            forall |i: int| 0 <= i < increments.len() ==> #[trigger] increments[i] <= 1u8,
            forall |i: int| 0 <= i < k as int ==> -100 <= #[trigger] nums[i] <= 100,
            forall |i: int, j: int| 0 <= i <= j < k as int ==> nums[i] <= nums[j],
            k > 0 ==> nums[k as int - 1] == cur,
        decreases n - k,
    {
        let inc = increments[k];
        let next_val: i32 = if inc == 1u8 && cur < 100 { cur + 1 } else { cur };
        assert(-100 <= next_val <= 100);
        assert(cur <= next_val);
        nums.push(next_val);
        cur = next_val;
        k = k + 1;
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_increments(rng: &mut Rng, n: usize, mode: usize) -> (i32, Vec<u8>) {
    let mut incs: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 => {
            // All same value
            let v = rng.gen_range_i32(-100, 100);
            for _ in 0..n { incs.push(0); }
            (v, incs)
        }
        1 => {
            // Strictly increasing from base
            let base = -100i32;
            for _ in 0..n { incs.push(1); }
            (base, incs)
        }
        2 => {
            // Mostly zeros with occasional increments
            let base = rng.gen_range_i32(-100, 0);
            for _ in 0..n {
                if rng.next_u64() % 10 == 0 { incs.push(1); } else { incs.push(0); }
            }
            (base, incs)
        }
        3 => {
            // Two distinct values: [v, v, v, w, w, w]
            let base = rng.gen_range_i32(-100, 99);
            let split = if n > 1 { rng.gen_range_usize(1, n - 1) } else { 0 };
            for i in 0..n {
                if i == split { incs.push(1); } else { incs.push(0); }
            }
            (base, incs)
        }
        4 => {
            // All 100
            for _ in 0..n { incs.push(0); }
            (100, incs)
        }
        5 => {
            // All -100
            for _ in 0..n { incs.push(0); }
            (-100, incs)
        }
        6 => {
            // Alternating increments
            let base = -100i32;
            for i in 0..n { incs.push(if i % 2 == 0 { 1 } else { 0 }); }
            (base, incs)
        }
        7 => {
            // Random
            let base = rng.gen_range_i32(-100, 100);
            for _ in 0..n { incs.push((rng.next_u64() % 2) as u8); }
            (base, incs)
        }
        8 => {
            // Single element
            let base = rng.gen_range_i32(-100, 100);
            incs.push(0);
            (base, incs)
        }
        9 => {
            // Two elements same
            let base = rng.gen_range_i32(-100, 100);
            incs.push(0); incs.push(0);
            (base, incs)
        }
        _ => {
            // Two elements different
            let base = rng.gen_range_i32(-100, 99);
            incs.push(0); incs.push(1);
            (base, incs)
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 201, // ensures we stop at 100
            2 => 1000,
            3 => 2 + (t % 50),
            4 => 1,
            5 => 1,
            6 => 201,
            7 => 100 + (t % 500),
            8 => 1,
            9 => 2,
            _ => 2,
        };
        // Clamp to valid bounds
        let n = if n < 1 { 1 } else if n > 30_000 { 30_000 } else { n };

        let (base, incs) = build_increments(&mut rng, n, mode);
        let nums = generate_test_case(base, &incs);
        print_json(&nums);
    }
}