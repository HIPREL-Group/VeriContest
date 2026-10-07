use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 200_000,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        2 <= nums.len() <= 200_000,
        nums.len() == n,
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            2 <= n <= 200_000,
            values.len() == n,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -1_000_000_000 <= #[trigger] values[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v = values[i];
        assert(-1_000_000_000 <= v <= 1_000_000_000);
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp_val(v: i64) -> i32 {
    if v < -1_000_000_000 {
        -1_000_000_000
    } else if v > 1_000_000_000 {
        1_000_000_000
    } else {
        v as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        1 => {
            // strictly increasing entire array
            let start = rng.gen_range_i32(-1_000_000_000, 1_000_000_000 - n as i32);
            for i in 0..n {
                v.push(start + i as i32);
            }
        }
        2 => {
            // strictly decreasing
            let start = rng.gen_range_i32(-1_000_000_000 + n as i32, 1_000_000_000);
            for i in 0..n {
                v.push(start - i as i32);
            }
        }
        3 => {
            // two increasing halves [1..k][1..k]
            let k = n / 2;
            for i in 0..k {
                v.push(i as i32);
            }
            for i in 0..(n - k) {
                v.push(i as i32);
            }
        }
        4 => {
            // random small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
        }
        5 => {
            // full random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1_000_000_000, 1_000_000_000));
            }
        }
        6 => {
            // extreme bounds alternating
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(-1_000_000_000);
                } else {
                    v.push(1_000_000_000);
                }
            }
        }
        7 => {
            // increasing with plateau in middle
            let k = n / 3;
            for i in 0..k {
                v.push(i as i32);
            }
            for _ in 0..(n - 2 * k) {
                v.push(k as i32);
            }
            for i in 0..k {
                v.push((k + 1 + i) as i32);
            }
            while v.len() < n {
                v.push(0);
            }
            while v.len() > n {
                v.pop();
            }
        }
        8 => {
            // sawtooth: increasing runs of fixed length r
            let r = 2 + (rng.next_u64() as usize % 5);
            for i in 0..n {
                v.push((i % r) as i32);
            }
        }
        9 => {
            // two long increasing blocks with a break
            let half = n / 2;
            for i in 0..half {
                v.push(i as i32 - half as i32);
            }
            for i in 0..(n - half) {
                v.push(i as i32);
            }
        }
        10 => {
            // block of equal values
            let a = rng.gen_range_i32(-1000, 1000);
            for _ in 0..n {
                v.push(a);
            }
            // perturb a few
            let count = (n / 8).max(1);
            for _ in 0..count {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = rng.gen_range_i32(-1000, 1000);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    // Safety clamp
    for i in 0..v.len() {
        let x = v[i] as i64;
        v[i] = clamp_val(x);
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 2,
            1 => 3 + (t % 10),
            2 => 20 + (t % 30),
            3 => 100 + (t % 100),
            4 => 1000,
            5 => 5000,
            _ => 200_000,
        };
        let n = if n < 2 { 2 } else if n > 200_000 { 200_000 } else { n };

        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(n, &values);
        print_json(&nums);
    }
}