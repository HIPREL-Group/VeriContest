use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100000,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] < n as i32,
    ensures
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < nums.len(),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n <= 100000,
            n >= 1,
            nums.len() == k,
            values.len() == n,
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] < n as i32,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == values[i],
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }
    assert(nums.len() == n);
    assert(forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == values[i]);
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
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        1 => {
            // all equal to n-1 (but need < n, so n-1 valid)
            for _ in 0..n {
                v.push((n - 1) as i32);
            }
        }
        2 => {
            // identity-ish: value = i, but capped so < n
            for i in 0..n {
                v.push((i % n) as i32);
            }
        }
        3 => {
            // reversed
            for i in 0..n {
                v.push((n - 1 - i) as i32);
            }
        }
        4 => {
            // random values in [0, n-1]
            for _ in 0..n {
                v.push(rng.gen_range_usize(0, n - 1) as i32);
            }
        }
        5 => {
            // half 0s, half n-1s
            for i in 0..n {
                if i < n / 2 {
                    v.push(0);
                } else {
                    v.push((n - 1) as i32);
                }
            }
        }
        6 => {
            // alternating 0 and 1 (if n >= 2)
            for i in 0..n {
                let val = (i % 2) as i32;
                if val < n as i32 {
                    v.push(val);
                } else {
                    v.push(0);
                }
            }
        }
        7 => {
            // values all equal to some k in [0, n-1]
            let k = rng.gen_range_usize(0, n - 1) as i32;
            for _ in 0..n {
                v.push(k);
            }
        }
        8 => {
            // mostly zeros with one n-1
            for i in 0..n {
                if i == n / 2 {
                    v.push((n - 1) as i32);
                } else {
                    v.push(0);
                }
            }
        }
        9 => {
            // sorted ascending random in range
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            for _ in 0..n {
                tmp.push(rng.gen_range_usize(0, n - 1) as i32);
            }
            tmp.sort();
            v = tmp;
        }
        _ => {
            // random
            for _ in 0..n {
                v.push(rng.gen_range_usize(0, n - 1) as i32);
            }
        }
    }
    // sanity clamp (should already be fine)
    for i in 0..v.len() {
        if v[i] < 0 {
            v[i] = 0;
        }
        if v[i] >= n as i32 {
            v[i] = (n - 1) as i32;
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3 + (t % 10),
            3 => 50 + (t % 50),
            4 => 1000,
            5 => 10000,
            6 => 100000,
            _ => 10,
        };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(n, &values);
        print_json(&nums);
    }
}