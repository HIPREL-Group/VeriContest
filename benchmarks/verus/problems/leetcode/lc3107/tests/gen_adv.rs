use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 200000,
        1 <= k <= 1000000000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000000,
    ensures
        ({
            let (nums, kk) = result;
            &&& 1 <= nums.len() <= 200000
            &&& 1 <= kk <= 1000000000
            &&& forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000
        }),
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1000000000,
            forall |j: int| 0 <= j < i ==> 1 <= #[trigger] nums[j] <= 1000000000,
            forall |j: int| 0 <= j < i ==> nums[j] == values[j],
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    (nums, k)
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

fn build(values: Vec<i32>, k: i32) {
    let (nums, kk) = generate_test_case(&values, k);
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", kk);
}

fn mode_case(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // single element
            let v = rng.gen_i32(1, 1_000_000_000);
            let k = rng.gen_i32(1, 1_000_000_000);
            (vec![v], k)
        }
        1 => {
            // all equal to k
            let k = rng.gen_i32(1, 1_000_000_000);
            let n = rng.gen_usize(1, 100);
            (vec![k; n], k)
        }
        2 => {
            // all equal, but != k
            let v = rng.gen_i32(1, 1_000_000_000);
            let k = rng.gen_i32(1, 1_000_000_000);
            let n = rng.gen_usize(1, 50);
            (vec![v; n], k)
        }
        3 => {
            // sorted ascending
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            let mut cur = rng.gen_i32(1, 100);
            for _ in 0..n {
                v.push(cur);
                cur = (cur + rng.gen_i32(0, 10)).min(1_000_000_000);
            }
            let k = rng.gen_i32(1, 1_000_000_000);
            (v, k)
        }
        4 => {
            // sorted descending
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            let mut cur = rng.gen_i32(500_000_000, 1_000_000_000);
            for _ in 0..n {
                v.push(cur);
                cur = (cur - rng.gen_i32(0, 10)).max(1);
            }
            let k = rng.gen_i32(1, 1_000_000_000);
            (v, k)
        }
        5 => {
            // k = 1 (boundary)
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(1, 1_000_000_000)); }
            (v, 1)
        }
        6 => {
            // k = 1_000_000_000
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(1, 1_000_000_000)); }
            (v, 1_000_000_000)
        }
        7 => {
            // even length - higher median rule
            let n = 2 * rng.gen_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(1, 1_000_000_000)); }
            let k = rng.gen_i32(1, 1_000_000_000);
            (v, k)
        }
        8 => {
            // odd length
            let n = 2 * rng.gen_usize(0, 50) + 1;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(1, 1_000_000_000)); }
            let k = rng.gen_i32(1, 1_000_000_000);
            (v, k)
        }
        9 => {
            // extreme values
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(1); } else { v.push(1_000_000_000); }
            }
            let k = rng.gen_i32(1, 1_000_000_000);
            (v, k)
        }
        _ => {
            let n = rng.gen_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_i32(1, 1_000_000_000)); }
            let k = rng.gen_i32(1, 1_000_000_000);
            let _ = t;
            (v, k)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (v, k) = mode_case(&mut rng, mode, t);
        build(v, k);
    }
}