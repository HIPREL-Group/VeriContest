use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 10_000,
        forall|i: int| 0 <= i < vals.len() ==>
            -100_000 <= #[trigger] vals[i] <= 100_000,
    ensures
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==>
            -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall|k: int| 0 <= k < vals.len() ==>
                -100_000 <= #[trigger] vals[k] <= 100_000,
        decreases n - i,
    {
        nums.push(vals[i]);
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
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
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

fn clamp(x: i32) -> i32 {
    if x < -100_000 {
        -100_000
    } else if x > 100_000 {
        100_000
    } else {
        x
    }
}

fn build_sorted(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i32 = rng.gen_range_i32(-100_000, -50_000);
    for _ in 0..n {
        v.push(cur);
        let step = rng.gen_range_i32(0, 200);
        cur = clamp(cur.saturating_add(step));
    }
    v
}

fn build_reverse_sorted(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = build_sorted(n, rng);
    v.reverse();
    v
}

fn build_random(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(-100_000, 100_000));
    }
    v
}

fn build_almost_sorted(n: usize, rng: &mut Rng, swaps: usize) -> Vec<i32> {
    let mut v = build_sorted(n, rng);
    for _ in 0..swaps {
        if n >= 2 {
            let i = rng.gen_range_usize(0, n - 1);
            let j = rng.gen_range_usize(0, n - 1);
            v.swap(i, j);
        }
    }
    v
}

fn build_constant(n: usize, rng: &mut Rng) -> Vec<i32> {
    let c = rng.gen_range_i32(-100_000, 100_000);
    vec![c; n]
}

fn build_single_dip(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = build_sorted(n, rng);
    if n >= 2 {
        let i = rng.gen_range_usize(0, n - 1);
        v[i] = rng.gen_range_i32(-100_000, 100_000);
    }
    v
}

fn build_unsorted_middle(n: usize, rng: &mut Rng) -> Vec<i32> {
    if n < 4 {
        return build_random(n, rng);
    }
    let mut v = build_sorted(n, rng);
    let lo = n / 4;
    let hi = 3 * n / 4;
    for i in lo..hi {
        v[i] = rng.gen_range_i32(-100_000, 100_000);
    }
    v
}

fn build_extremes(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 {
            v.push(-100_000);
        } else {
            v.push(100_000);
        }
    }
    v
}

fn build_two_swap(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = build_sorted(n, rng);
    if n >= 2 {
        let i = rng.gen_range_usize(0, n - 1);
        let mut j = rng.gen_range_usize(0, n - 1);
        if i == j && n >= 2 {
            j = (j + 1) % n;
        }
        v.swap(i, j);
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
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 2 + (t % 50),
            2 => 10_000,
            3 => 100 + (t % 200),
            4 => if t % 2 == 0 { 1 } else { 2 },
            5 => 500,
            6 => 50 + (t % 100),
            7 => 3 + (t % 30),
            8 => 9_999,
            _ => 20 + (t % 80),
        };

        let vals: Vec<i32> = match mode {
            0 => build_sorted(n, &mut rng),
            1 => build_reverse_sorted(n, &mut rng),
            2 => build_random(n, &mut rng),
            3 => build_almost_sorted(n, &mut rng, 1 + (t % 3)),
            4 => build_constant(n, &mut rng),
            5 => build_single_dip(n, &mut rng),
            6 => build_unsorted_middle(n, &mut rng),
            7 => build_extremes(n),
            8 => build_two_swap(n, &mut rng),
            _ => build_random(n, &mut rng),
        };

        // Safety clamp
        let mut safe: Vec<i32> = Vec::with_capacity(vals.len());
        for x in &vals {
            safe.push(clamp(*x));
        }
        if safe.is_empty() {
            safe.push(0);
        }
        if safe.len() > 10_000 {
            safe.truncate(10_000);
        }

        let nums = generate_test_case(&safe);
        print_json(&nums);
    }
}