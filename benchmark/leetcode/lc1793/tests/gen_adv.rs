use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    values: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        0 <= k < n as i32,
        values.len() == n,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 20_000,
    ensures
        ({
            let (nums, kk) = result;
            &&& 1 <= nums.len() <= 100_000
            &&& nums.len() == n
            &&& (forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 20_000)
            &&& 0 <= kk < nums.len() as i32
            &&& kk == k
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            n == values.len(),
            1 <= n <= 100_000,
            0 <= idx <= n,
            nums.len() == idx,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 20_000,
            forall|i: int| 0 <= i < idx as int ==> nums[i] == values[i],
            forall|i: int| 0 <= i < idx as int ==> 1 <= #[trigger] nums[i] <= 20_000,
        decreases n - idx,
    {
        let v = values[idx];
        assert(1 <= v <= 20_000);
        nums.push(v);
        idx = idx + 1;
        assert(forall|i: int| 0 <= i < idx as int ==> nums[i] == values[i]);
        assert forall|i: int| 0 <= i < idx as int implies 1 <= #[trigger] nums[i] <= 20_000 by {
            assert(nums[i] == values[i]);
        }
    }

    (nums, k)
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
        (lo as i64 + v as i64) as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < 1 { 1 } else if v > 20_000 { 20_000 } else { v }
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 20);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 20_000));
            }
            (n, k, v)
        }
        1 => {
            // n = 1
            (1, 0, vec![rng.gen_range_i32(1, 20_000)])
        }
        2 => {
            // all equal
            let n = rng.gen_range_usize(1, 1000);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let x = rng.gen_range_i32(1, 20_000);
            let v = vec![x; n];
            (n, k, v)
        }
        3 => {
            // k at start
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 20_000));
            }
            (n, 0, v)
        }
        4 => {
            // k at end
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 20_000));
            }
            (n, (n - 1) as i32, v)
        }
        5 => {
            // nums[k] is minimum
            let n = rng.gen_range_usize(2, 500);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(100, 20_000));
            }
            v[k as usize] = 1;
            (n, k, v)
        }
        6 => {
            // nums[k] is maximum
            let n = rng.gen_range_usize(2, 500);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v[k as usize] = 20_000;
            (n, k, v)
        }
        7 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 500);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(clamp_val((i as i32) + 1));
            }
            (n, k, v)
        }
        8 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 500);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(clamp_val((n as i32) - (i as i32)));
            }
            (n, k, v)
        }
        9 => {
            // large n random
            let n = 100_000;
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 20_000));
            }
            (n, k, v)
        }
        10 => {
            // alternating
            let n = rng.gen_range_usize(2, 1000);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 20_000 });
            }
            (n, k, v)
        }
        _ => {
            // mountain around k
            let n = rng.gen_range_usize(2, 1000);
            let k = rng.gen_range_usize(0, n - 1) as i32;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let d = ((i as i32) - k).abs();
                v.push(clamp_val(20_000 - d));
            }
            let _ = t;
            (n, k, v)
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k, values) = gen_mode(&mut rng, mode, t);
        let (nums, kk) = generate_test_case(n, k, &values);
        print_json(&nums, kk);
    }
}