use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    base: i32,
    increments: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 100_000,
        increments.len() == n,
        1 <= base <= 10_000,
        forall|i: int| 0 <= i < increments.len() ==> 0 <= #[trigger] increments[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < increments.len() ==> increments[i] <= increments[j],
        increments[0] == 0,
        increments[(n - 1) as int] as int + base as int <= 10_000,
    ensures
        2 <= nums@.len() <= 100_000,
        nums@.len() == n,
        forall|i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < nums@.len() ==> nums@[i] <= nums@[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            k <= n,
            nums.len() == k,
            2 <= n <= 100_000,
            increments.len() == n,
            1 <= base <= 10_000,
            forall|i: int| 0 <= i < increments.len() ==> 0 <= #[trigger] increments[i] <= 10_000,
            forall|i: int, j: int| 0 <= i <= j < increments.len() ==> increments[i] <= increments[j],
            increments[(n - 1) as int] as int + base as int <= 10_000,
            forall|i: int| 0 <= i < k as int ==> #[trigger] nums[i] as int == base as int + increments[i] as int,
            forall|i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 10_000,
        decreases n - k,
    {
        let v: i32 = base + increments[k];
        assert(increments[k as int] <= increments[(n - 1) as int]);
        assert(v as int <= 10_000);
        nums.push(v);
        k = k + 1;
    }

    proof {
        assert forall|i: int, j: int| 0 <= i <= j < nums@.len() implies nums@[i] <= nums@[j] by {
            assert(nums[i] as int == base as int + increments[i] as int);
            assert(nums[j] as int == base as int + increments[j] as int);
            assert(increments[i] <= increments[j]);
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(n: usize, base: i32, increments_raw: Vec<i32>) -> Vec<i32> {
    // increments must be len n, sorted nondec, [0] = 0, all in [0,10000], base+incs[n-1] <= 10000.
    let mut incs = increments_raw;
    if incs.len() != n {
        incs = vec![0i32; n];
    }
    // clamp each to [0, 10000 - base]
    let max_inc = 10_000i32 - base;
    for v in incs.iter_mut() {
        if *v < 0 { *v = 0; }
        if *v > max_inc { *v = max_inc; }
    }
    incs.sort();
    incs[0] = 0;
    // re-sort in case
    incs.sort();
    generate_test_case(n, base, &incs)
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn mode_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_usize(2, 10);
            let base = rng.gen_i32(1, 100);
            let max_inc = 10_000 - base;
            let mut incs: Vec<i32> = (0..n).map(|_| rng.gen_i32(0, max_inc.min(100))).collect();
            incs[0] = 0;
            (n, base, incs)
        }
        1 => {
            // all same value
            let n = rng.gen_usize(2, 1000);
            let base = rng.gen_i32(1, 10_000);
            let incs = vec![0i32; n];
            (n, base, incs)
        }
        2 => {
            // min size = 2
            let n = 2;
            let base = rng.gen_i32(1, 5000);
            let max_inc = 10_000 - base;
            let incs = vec![0i32, rng.gen_i32(0, max_inc)];
            (n, base, incs)
        }
        3 => {
            // max size
            let n = 100_000;
            let base = 1i32;
            let mut incs: Vec<i32> = (0..n).map(|_| rng.gen_i32(0, 9_999)).collect();
            incs[0] = 0;
            (n, base, incs)
        }
        4 => {
            // all value 1
            let n = rng.gen_usize(2, 500);
            (n, 1i32, vec![0i32; n])
        }
        5 => {
            // all value 10000
            let n = rng.gen_usize(2, 500);
            (n, 10_000i32, vec![0i32; n])
        }
        6 => {
            // two distinct values
            let n = rng.gen_usize(2, 200);
            let base = rng.gen_i32(1, 5000);
            let delta = rng.gen_i32(0, 10_000 - base);
            let k = rng.gen_usize(1, n - 1);
            let mut incs = vec![0i32; n];
            for i in k..n { incs[i] = delta; }
            (n, base, incs)
        }
        7 => {
            // strictly increasing ramp
            let n = rng.gen_usize(2, 100);
            let base = 1i32;
            let max_inc = 9_999i32.min((n as i32 - 1).max(0));
            let step = if n <= 1 { 0 } else { max_inc / (n as i32 - 1) };
            let incs: Vec<i32> = (0..n).map(|i| i as i32 * step).collect();
            (n, base, incs)
        }
        8 => {
            // extreme range 1..10000 size 10000
            let n = 10_000usize;
            let base = 1i32;
            let incs: Vec<i32> = (0..n).map(|i| (i as i32).min(9_999)).collect();
            (n, base, incs)
        }
        9 => {
            // random medium
            let n = rng.gen_usize(50, 2000);
            let base = rng.gen_i32(1, 9_000);
            let max_inc = 10_000 - base;
            let incs: Vec<i32> = (0..n).map(|_| rng.gen_i32(0, max_inc)).collect();
            (n, base, incs)
        }
        _ => {
            let n = rng.gen_usize(2, 500 + t % 100);
            let base = rng.gen_i32(1, 10_000);
            let max_inc = 10_000 - base;
            let incs: Vec<i32> = (0..n).map(|_| rng.gen_i32(0, max_inc)).collect();
            (n, base, incs)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, base, incs) = mode_case(&mut rng, mode, t);
        let nums = build(n, base, incs);
        print_json(&nums);
    }
}