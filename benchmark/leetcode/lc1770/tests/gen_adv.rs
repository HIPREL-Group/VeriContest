use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    nums_vals: &Vec<i32>,
    mults_vals: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= m <= 300,
        m <= n <= 100_000,
        nums_vals.len() == n,
        mults_vals.len() == m,
        forall|i: int| 0 <= i < nums_vals.len() ==> -1000 <= #[trigger] nums_vals[i] <= 1000,
        forall|i: int| 0 <= i < mults_vals.len() ==> -1000 <= #[trigger] mults_vals[i] <= 1000,
    ensures
        ({
            let (nums, mults) = result;
            &&& mults.len() >= 1
            &&& mults.len() <= 300
            &&& nums.len() >= mults.len()
            &&& nums.len() <= 100_000
            &&& (forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000)
            &&& (forall|i: int| 0 <= i < mults.len() ==> -1000 <= #[trigger] mults[i] <= 1000)
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            nums.len() == i,
            nums_vals.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == nums_vals[k],
            forall|k: int| 0 <= k < nums_vals.len() ==> -1000 <= #[trigger] nums_vals[k] <= 1000,
        decreases n - i,
    {
        nums.push(nums_vals[i]);
        i = i + 1;
    }

    let mut mults: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            j <= m,
            mults.len() == j,
            mults_vals.len() == m,
            forall|k: int| 0 <= k < j as int ==> #[trigger] mults[k] == mults_vals[k],
            forall|k: int| 0 <= k < mults_vals.len() ==> -1000 <= #[trigger] mults_vals[k] <= 1000,
        decreases m - j,
    {
        mults.push(mults_vals[j]);
        j = j + 1;
    }

    (nums, mults)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(nums: Vec<i32>, mults: Vec<i32>) -> (Vec<i32>, Vec<i32>) {
    let n = nums.len();
    let m = mults.len();
    assert!(m >= 1 && m <= 300);
    assert!(n >= m && n <= 100_000);
    for &v in &nums {
        assert!(v >= -1000 && v <= 1000);
    }
    for &v in &mults {
        assert!(v >= -1000 && v <= 1000);
    }
    generate_test_case(n, m, &nums, &mults)
}

fn print_json(nums: &[i32], mults: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"multipliers\":[");
    for i in 0..mults.len() {
        if i > 0 { print!(","); }
        print!("{}", mults[i]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // Minimal: m=1, n=1
            let v = rng.gen_range_i32(-1000, 1000);
            let mv = rng.gen_range_i32(-1000, 1000);
            (vec![v], vec![mv])
        }
        1 => {
            // m = n (all picked)
            let m = rng.gen_range_usize(1, 50);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..m {
                nums.push(rng.gen_range_i32(-1000, 1000));
                mults.push(rng.gen_range_i32(-1000, 1000));
            }
            (nums, mults)
        }
        2 => {
            // Large n, small m
            let n = rng.gen_range_usize(1000, 5000);
            let m = rng.gen_range_usize(1, 10);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 1000));
            }
            for _ in 0..m {
                mults.push(rng.gen_range_i32(-1000, 1000));
            }
            (nums, mults)
        }
        3 => {
            // All positive
            let m = rng.gen_range_usize(1, 30);
            let n = rng.gen_range_usize(m, m + 50);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(0, 1000));
            }
            for _ in 0..m {
                mults.push(rng.gen_range_i32(0, 1000));
            }
            (nums, mults)
        }
        4 => {
            // All negative
            let m = rng.gen_range_usize(1, 30);
            let n = rng.gen_range_usize(m, m + 50);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 0));
            }
            for _ in 0..m {
                mults.push(rng.gen_range_i32(-1000, 0));
            }
            (nums, mults)
        }
        5 => {
            // Extremes
            let m = rng.gen_range_usize(1, 20);
            let n = rng.gen_range_usize(m, m + 30);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                let r = rng.next_u64() % 3;
                nums.push(if r == 0 { -1000 } else if r == 1 { 1000 } else { 0 });
            }
            for _ in 0..m {
                let r = rng.next_u64() % 3;
                mults.push(if r == 0 { -1000 } else if r == 1 { 1000 } else { 0 });
            }
            (nums, mults)
        }
        6 => {
            // Max m
            let m = 300;
            let n = rng.gen_range_usize(m, 1000);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 1000));
            }
            for _ in 0..m {
                mults.push(rng.gen_range_i32(-1000, 1000));
            }
            (nums, mults)
        }
        7 => {
            // Sorted ascending nums
            let m = rng.gen_range_usize(1, 20);
            let n = rng.gen_range_usize(m, m + 30);
            let mut nums: Vec<i32> = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 1000));
            }
            nums.sort();
            let mut mults = Vec::new();
            for _ in 0..m {
                mults.push(rng.gen_range_i32(-1000, 1000));
            }
            (nums, mults)
        }
        8 => {
            // Mults alternating
            let m = rng.gen_range_usize(2, 50);
            let n = rng.gen_range_usize(m, m + 30);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 1000));
            }
            for i in 0..m {
                mults.push(if i % 2 == 0 { 1000 } else { -1000 });
            }
            (nums, mults)
        }
        9 => {
            // All zeros
            let m = rng.gen_range_usize(1, 20);
            let n = rng.gen_range_usize(m, m + 20);
            (vec![0i32; n], vec![0i32; m])
        }
        _ => {
            // Random general
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(m, m + 200);
            let mut nums = Vec::new();
            let mut mults = Vec::new();
            for _ in 0..n {
                nums.push(rng.gen_range_i32(-1000, 1000));
            }
            for _ in 0..m {
                mults.push(rng.gen_range_i32(-1000, 1000));
            }
            (nums, mults)
        }
    }
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
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (nums, mults) = gen_mode(&mut rng, mode);
        let (nums, mults) = build(nums, mults);
        print_json(&nums, &mults);
    }
}