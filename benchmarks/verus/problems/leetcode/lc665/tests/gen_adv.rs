use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 10_000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> -100_000 <= #[trigger] fillers[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 10_000,
        forall|i: int| 0 <= i < result.0.len() ==> -100_000 <= #[trigger] result.0[i] <= 100_000,
        result.1 < result.0.len(),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            fillers.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == fillers[k],
            forall|k: int| 0 <= k < fillers.len() ==> -100_000 <= #[trigger] fillers[k] <= 100_000,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }

    assert(nums.len() == n);
    assert(forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] == fillers[k]);

    let k: usize = 0;
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

fn build_fillers_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(-100_000, 100_000));
    }
    v
}

fn build_sorted(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i32 = -100_000;
    for _ in 0..n {
        let step = rng.gen_range_i32(0, 20);
        cur = (cur as i64 + step as i64).min(100_000) as i32;
        v.push(cur);
    }
    v
}

fn build_one_dip(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = build_sorted(rng, n);
    if n >= 2 {
        let idx = rng.gen_range_usize(1, n - 1);
        v[idx] = rng.gen_range_i32(-100_000, v[idx - 1].saturating_sub(1).max(-100_000));
    }
    v
}

fn build_two_dips(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = build_sorted(rng, n);
    if n >= 4 {
        let i1 = rng.gen_range_usize(1, n / 2);
        let i2 = rng.gen_range_usize(n / 2 + 1, n - 1);
        if v[i1 - 1] > -100_000 {
            v[i1] = rng.gen_range_i32(-100_000, v[i1 - 1] - 1);
        }
        if v[i2 - 1] > -100_000 {
            v[i2] = rng.gen_range_i32(-100_000, v[i2 - 1] - 1);
        }
    }
    v
}

fn build_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i32 = 100_000;
    for _ in 0..n {
        v.push(cur);
        cur = (cur - 1).max(-100_000);
    }
    v
}

fn build_all_same(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn build_first_big(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = build_sorted(rng, n);
    if n >= 1 {
        v[0] = 100_000;
    }
    v
}

fn build_last_small(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = build_sorted(rng, n);
    if n >= 1 {
        v[n - 1] = -100_000;
    }
    v
}

fn build_leet_example1() -> Vec<i32> {
    vec![4, 2, 3]
}
fn build_leet_example2() -> Vec<i32> {
    vec![4, 2, 1]
}
fn build_3_4_2_3() -> Vec<i32> {
    vec![3, 4, 2, 3]
}

fn print_json(nums: &[i32], k: usize) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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

    let total = 200usize;
    let modes = 12usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(4, 20),
            4 => rng.gen_range_usize(50, 200),
            5 => 10_000,
            6 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(2, 100),
        };

        let fillers = match mode {
            0 => build_fillers_random(&mut rng, n),
            1 => build_sorted(&mut rng, n),
            2 => build_one_dip(&mut rng, n),
            3 => build_two_dips(&mut rng, n),
            4 => build_decreasing(n),
            5 => build_all_same(n, rng.gen_range_i32(-100_000, 100_000)),
            6 => build_first_big(&mut rng, n),
            7 => build_last_small(&mut rng, n),
            8 => {
                let ex = build_leet_example1();
                ex
            }
            9 => {
                let ex = build_leet_example2();
                ex
            }
            10 => {
                let ex = build_3_4_2_3();
                ex
            }
            _ => build_fillers_random(&mut rng, n),
        };

        let actual_n = fillers.len();
        if actual_n < 1 || actual_n > 10_000 {
            continue;
        }
        let mut valid = true;
        for &x in &fillers {
            if x < -100_000 || x > 100_000 {
                valid = false;
                break;
            }
        }
        if !valid {
            continue;
        }

        let (nums, k) = generate_test_case(actual_n, &fillers);
        print_json(&nums, k);
    }
}