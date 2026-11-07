use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    index_difference: i32,
    value_difference: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= values.len() <= 100,
        0 <= index_difference <= 100,
        0 <= value_difference <= 50,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 50,
    ensures
        1 <= result.0.len() <= 100,
        0 <= result.1 <= 100,
        0 <= result.2 <= 50,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 50,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 50,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    (nums, index_difference, value_difference)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // single element
            let v = rng.gen_range_i32(0, 50);
            (vec![v], 0, 0)
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            (vec![0; n], rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 50))
        }
        2 => {
            // all 50s
            let n = rng.gen_range_usize(1, 100);
            (vec![50; n], rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 50))
        }
        3 => {
            // extremes at ends
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![25i32; n];
            v[0] = 0;
            v[n - 1] = 50;
            (v, rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, 50))
        }
        4 => {
            // indexDifference = 0, valueDifference = 0 (always solvable)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 50));
            }
            (v, 0, 0)
        }
        5 => {
            // large indexDifference (> n)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 50));
            }
            (v, rng.gen_range_i32(n as i32, 100), rng.gen_range_i32(0, 50))
        }
        6 => {
            // valueDifference = 50 (only 0..50 pair works)
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 50 });
            }
            (v, rng.gen_range_i32(0, n as i32 - 1), 50)
        }
        7 => {
            // alternating pattern
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { rng.gen_range_i32(0, 10) } else { rng.gen_range_i32(40, 50) });
            }
            (v, rng.gen_range_i32(0, 5), rng.gen_range_i32(20, 50))
        }
        8 => {
            // n = 100 max
            let n = 100usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 50));
            }
            (v, rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 50))
        }
        9 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let val = ((i as i32) * 50 / (if n > 1 { n as i32 - 1 } else { 1 })).min(50).max(0);
                v.push(val);
            }
            (v, rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 50))
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 50));
            }
            (v, rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 50))
        }
    }
}

fn print_json(nums: &[i32], idx_diff: i32, val_diff: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"index_difference\":{},\"value_difference\":{}}}", idx_diff, val_diff);
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
        let (values, idx_diff, val_diff) = build(&mut rng, mode);
        // Safety clamp (already within bounds but be explicit)
        let mut clamped: Vec<i32> = Vec::with_capacity(values.len());
        for x in &values {
            let mut c = *x;
            if c < 0 { c = 0; }
            if c > 50 { c = 50; }
            clamped.push(c);
        }
        if clamped.is_empty() {
            clamped.push(0);
        }
        if clamped.len() > 100 {
            clamped.truncate(100);
        }
        let mut id = idx_diff;
        if id < 0 { id = 0; }
        if id > 100 { id = 100; }
        let mut vd = val_diff;
        if vd < 0 { vd = 0; }
        if vd > 50 { vd = 50; }

        let (nums, idx_out, val_out) = generate_test_case(&clamped, id, vd);
        print_json(&nums, idx_out, val_out);
    }
}