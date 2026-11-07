use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 10_000,
        forall|i: int| 0 <= i < values.len() ==>
            -1_000_000_000 <= #[trigger] values[i] <= 1_000_000_000,
        0 <= k <= 10_000,
    ensures
        1 <= res.0.len() <= 10_000,
        forall|i: int| 1 <= i < res.0.len() ==>
            -1_000_000_000 <= #[trigger] res.0[i] <= 1_000_000_000,
        0 <= res.1 <= 10_000,
        res.1 == k,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < i as int ==> nums[j] == values[j],
            forall|j: int| 0 <= j < values.len() ==>
                -1_000_000_000 <= #[trigger] values[j] <= 1_000_000_000,
        decreases values.len() - i,
    {
        nums.push(values[i]);
        i = i + 1;
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi { return lo; }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        if lo >= hi { return lo; }
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn clamp_i32(v: i64) -> i32 {
    if v < -1_000_000_000 { -1_000_000_000 }
    else if v > 1_000_000_000 { 1_000_000_000 }
    else { v as i32 }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(clamp_i32(rng.gen_range_i64(-1_000_000_000, 1_000_000_000)));
    }
    v
}

fn build_all_same(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(val); }
    v
}

fn build_all_distinct(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(i as i32 - (n as i32) / 2);
    }
    v
}

fn build_duplicate_at_distance(n: usize, val: i32, i: usize, j: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut counter: i64 = -500_000;
    for idx in 0..n {
        if idx == i || idx == j {
            v.push(val);
        } else {
            // avoid val
            if counter as i32 == val { counter += 1; }
            v.push(counter as i32);
            counter += 1;
        }
    }
    v
}

fn build_small_range(rng: &mut Rng, n: usize, range: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(clamp_i32(rng.gen_range_i64(-range, range)));
    }
    v
}

fn build_alternating(n: usize, a: i32, b: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn pick_test(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 20);
            let k = rng.gen_range_usize(0, 20) as i32;
            (build_random(rng, n), k)
        }
        1 => {
            // all same, various k
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_usize(0, n) as i32;
            (build_all_same(n, 7), k)
        }
        2 => {
            // all distinct
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_usize(0, 10_000) as i32;
            (build_all_distinct(n), k)
        }
        3 => {
            // duplicate exactly at distance k
            let n = rng.gen_range_usize(5, 100);
            let k = rng.gen_range_usize(1, n - 1) as i32;
            let i = 0usize;
            let j = k as usize;
            (build_duplicate_at_distance(n, 42, i, j), k)
        }
        4 => {
            // duplicate at distance k+1 (should return false for that pair)
            let n = rng.gen_range_usize(5, 100);
            let k = rng.gen_range_usize(1, (n - 2).max(1)) as i32;
            let i = 0usize;
            let j = (k as usize) + 1;
            if j < n {
                (build_duplicate_at_distance(n, 42, i, j), k)
            } else {
                (build_random(rng, n), k)
            }
        }
        5 => {
            // large n
            let n = 10_000usize;
            let k = rng.gen_range_usize(0, 10_000) as i32;
            (build_all_distinct(n), k)
        }
        6 => {
            // k = 0
            let n = rng.gen_range_usize(1, 200);
            (build_random(rng, n), 0)
        }
        7 => {
            // single element
            let n = 1usize;
            let k = rng.gen_range_usize(0, 10_000) as i32;
            (build_random(rng, n), k)
        }
        8 => {
            // small range many dups
            let n = rng.gen_range_usize(10, 500);
            let k = rng.gen_range_usize(0, 20) as i32;
            (build_small_range(rng, n, 3), k)
        }
        9 => {
            // alternating
            let n = rng.gen_range_usize(2, 200);
            let k = rng.gen_range_usize(0, 5) as i32;
            (build_alternating(n, 1, 2), k)
        }
        10 => {
            // extreme values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let pick = rng.gen_range_i64(0, 3);
                let val = match pick {
                    0 => 1_000_000_000i32,
                    1 => -1_000_000_000i32,
                    2 => 0i32,
                    _ => clamp_i32(rng.gen_range_i64(-1_000_000_000, 1_000_000_000)),
                };
                v.push(val);
            }
            let k = rng.gen_range_usize(0, n) as i32;
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_usize(0, 100) as i32;
            (build_random(rng, n), k)
        }
    }
    .clone_into_result(idx)
}

// trick: make pick_test return directly; use helper
trait CloneIntoResult {
    fn clone_into_result(self, _idx: usize) -> Self;
}
impl CloneIntoResult for (Vec<i32>, i32) {
    fn clone_into_result(self, _idx: usize) -> Self { self }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (values, k) = pick_test(&mut rng, mode, t);
        let (nums, kk) = generate_test_case(&values, k);
        print_json(&nums, kk);
    }
}