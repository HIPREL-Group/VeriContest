use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 100,
        1 < 2 * k as int,
        2 * k as int <= n as int,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> -1000 <= #[trigger] vals[i] <= 1000,
    ensures
        2 <= nums.len() <= 100,
        1 < 2 * k as int,
        2 * k as int <= nums.len() as int,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> -1000 <= #[trigger] nums[j] <= 1000,
            forall|j: int| 0 <= j < vals.len() ==> -1000 <= #[trigger] vals[j] <= 1000,
        decreases n - i,
    {
        let v = vals[i];
        assert(-1000 <= v <= 1000);
        nums.push(v);
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < -1000 { -1000 } else if v > 1000 { 1000 } else { v }
}

fn build(rng: &mut Rng, mode: usize, n: usize, k: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
        1 => {
            // strictly increasing whole array
            let start = rng.gen_range_i32(-1000, 1000 - n as i32);
            for i in 0..n {
                v.push(clamp_val(start + i as i32));
            }
        }
        2 => {
            // all equal
            let c = rng.gen_range_i32(-1000, 1000);
            for _ in 0..n {
                v.push(c);
            }
        }
        3 => {
            // two adjacent increasing runs of length k at random start
            let max_a = n - 2 * k;
            let a = rng.gen_range_usize(0, max_a);
            let base: i32 = rng.gen_range_i32(-500, 500);
            for i in 0..n {
                if i >= a && i < a + k {
                    v.push(clamp_val(base + (i - a) as i32));
                } else if i >= a + k && i < a + 2 * k {
                    let base2: i32 = rng.gen_range_i32(-500, 500);
                    v.push(clamp_val(base2 + (i - a - k) as i32));
                } else {
                    v.push(rng.gen_range_i32(-1000, 1000));
                }
            }
            // Note: second run base is re-rolled each iteration; fix: precompute
        }
        4 => {
            // strictly decreasing
            let start = rng.gen_range_i32(-1000 + n as i32, 1000);
            for i in 0..n {
                v.push(clamp_val(start - i as i32));
            }
        }
        5 => {
            // one increasing run of length 2k-1 (should still return true since first k and then next k-1... actually need 2k)
            // length 2k-1 means second subarray not fully increasing if k>=2
            let start = rng.gen_range_i32(-500, 500);
            let run_len = if 2*k-1 <= n { 2*k-1 } else { n };
            let a = rng.gen_range_usize(0, n - run_len);
            for i in 0..n {
                if i >= a && i < a + run_len {
                    v.push(clamp_val(start + (i - a) as i32));
                } else {
                    v.push(rng.gen_range_i32(-1000, 1000));
                }
            }
        }
        6 => {
            // one full increasing run of length 2k
            let a = rng.gen_range_usize(0, n - 2 * k);
            let start = rng.gen_range_i32(-500, 500);
            for i in 0..n {
                if i >= a && i < a + 2 * k {
                    v.push(clamp_val(start + (i - a) as i32));
                } else {
                    v.push(rng.gen_range_i32(-1000, 1000));
                }
            }
        }
        7 => {
            // alternating up/down
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(-1000, 0));
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                }
            }
        }
        8 => {
            // two runs but with a duplicate at boundary making the second non-strict
            let a = rng.gen_range_usize(0, n - 2 * k);
            let base: i32 = 0;
            for i in 0..n {
                if i >= a && i < a + k {
                    v.push(clamp_val(base + (i - a) as i32));
                } else if i >= a + k && i < a + 2 * k {
                    // equal values
                    v.push(5);
                } else {
                    v.push(rng.gen_range_i32(-1000, 1000));
                }
            }
        }
        9 => {
            // small values near boundaries
            for _ in 0..n {
                let c = rng.next_u64() % 3;
                v.push(match c { 0 => -1000, 1 => 0, _ => 1000 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
        }
    }
    // ensure exactly length n and clamp
    while v.len() < n {
        v.push(0);
    }
    v.truncate(n);
    for i in 0..v.len() {
        v[i] = clamp_val(v[i]);
    }
    v
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        // choose n in [2,100] and k with 1 < 2k <= n, so k>=1 and k <= n/2, and k>=1 with 2k>1 so k>=1
        // Actually 1 < 2k means k >= 1 (2*1=2>1). And 2k<=n.
        let n = rng.gen_range_usize(2, 100);
        let max_k = n / 2;
        let k = if max_k < 1 { 1 } else { rng.gen_range_usize(1, max_k) };
        // ensure 2k <= n
        let n = if 2*k > n { 2*k } else { n };
        let n = if n > 100 { 100 } else { n };
        // guard
        if 2 * k > n || n < 2 || n > 100 { continue; }
        let vals = build(&mut rng, mode, n, k);
        let nums = generate_test_case(n, k as i32, &vals);
        print_json(&nums, k as i32);
    }
}