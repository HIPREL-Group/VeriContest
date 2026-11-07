use vstd::prelude::*;

verus! {

pub open spec fn sum_prefix(nums: Seq<i32>, end: nat) -> int
    decreases end,
{
    if end == 0 {
        0
    } else {
        sum_prefix(nums, (end - 1) as nat) + nums[(end - 1) as int] as int
    }
}

pub fn generate_test_case(
    vals: &Vec<i32>,
    target: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 20,
        forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1000,
        sum_prefix(vals@, vals.len() as nat) <= 1000,
        -1000 <= target <= 1000,
    ensures
        1 <= result.0.len() <= 20,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        sum_prefix(result.0@, result.0.len() as nat) <= 1000,
        -1000 <= result.1 <= 1000,
        result.1 == target,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < vals.len()
        invariant
            0 <= i <= vals.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> out[k] == vals[k],
            forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 1000,
        decreases vals.len() - i,
    {
        out.push(vals[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= vals@);
    }
    (out, target)
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

fn build_with_sum_cap(rng: &mut Rng, n: usize, cap: i32, max_elem: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let mut remaining: i32 = cap;
    for _ in 0..n {
        let upper = if remaining < max_elem { remaining } else { max_elem };
        let upper = if upper < 0 { 0 } else { upper };
        let x = rng.gen_range_i32(0, upper);
        v.push(x);
        remaining -= x;
        if remaining < 0 { remaining = 0; }
    }
    v
}

fn verify_and_fix(mut v: Vec<i32>) -> Vec<i32> {
    // ensure all <= 1000 and sum <= 1000
    let mut total: i64 = 0;
    for i in 0..v.len() {
        if v[i] < 0 { v[i] = 0; }
        if v[i] > 1000 { v[i] = 1000; }
        total += v[i] as i64;
    }
    // reduce elements until sum <= 1000
    let mut idx = 0;
    while total > 1000 && idx < v.len() {
        let excess = (total - 1000) as i32;
        if v[idx] >= excess {
            v[idx] -= excess;
            total -= excess as i64;
        } else {
            total -= v[idx] as i64;
            v[idx] = 0;
        }
        idx += 1;
    }
    v
}

fn make_case(rng: &mut Rng, mode: usize, _t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // all ones
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n { v.push(1i32); }
            let t = rng.gen_range_i32(-(n as i32), n as i32);
            (v, t)
        }
        1 => {
            // small values, random target
            let n = rng.gen_range_usize(1, 20);
            let max_each = 50i32;
            let v = build_with_sum_cap(rng, n, 1000, max_each);
            let v = verify_and_fix(v);
            let t = rng.gen_range_i32(-1000, 1000);
            (v, t)
        }
        2 => {
            // single element
            let x = rng.gen_range_i32(0, 1000);
            let t = if rng.next_u64() % 2 == 0 { x } else { -x };
            (vec![x], t)
        }
        3 => {
            // max length 20 with small elements
            let v = build_with_sum_cap(rng, 20, 1000, 50);
            let v = verify_and_fix(v);
            let t = rng.gen_range_i32(-1000, 1000);
            (v, t)
        }
        4 => {
            // all zeros
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n { v.push(0i32); }
            (v, 0)
        }
        5 => {
            // zeros + some values (edge case: 2^count_of_zeros multiplier)
            let n = rng.gen_range_usize(2, 20);
            let zeros = rng.gen_range_usize(1, n - 1);
            let mut v = Vec::new();
            for _ in 0..zeros { v.push(0i32); }
            let remain = n - zeros;
            let filler = build_with_sum_cap(rng, remain, 1000, 100);
            for x in filler { v.push(x); }
            let v = verify_and_fix(v);
            let sum: i32 = v.iter().sum();
            let t = rng.gen_range_i32(-sum, sum);
            (v, t)
        }
        6 => {
            // target equals sum
            let n = rng.gen_range_usize(1, 20);
            let v = build_with_sum_cap(rng, n, 1000, 100);
            let v = verify_and_fix(v);
            let t: i32 = v.iter().sum();
            (v, t)
        }
        7 => {
            // target = -sum
            let n = rng.gen_range_usize(1, 20);
            let v = build_with_sum_cap(rng, n, 1000, 100);
            let v = verify_and_fix(v);
            let s: i32 = v.iter().sum();
            (v, -s)
        }
        8 => {
            // target out of reach (= sum + 1 clamped)
            let n = rng.gen_range_usize(1, 20);
            let v = build_with_sum_cap(rng, n, 500, 50);
            let v = verify_and_fix(v);
            let s: i32 = v.iter().sum();
            let t = if s + 1 <= 1000 { s + 1 } else { 1000 };
            (v, t)
        }
        9 => {
            // target = 0
            let n = rng.gen_range_usize(1, 20);
            let v = build_with_sum_cap(rng, n, 1000, 100);
            let v = verify_and_fix(v);
            (v, 0)
        }
        _ => {
            // sum exactly 1000
            let n = rng.gen_range_usize(1, 20);
            let mut v = build_with_sum_cap(rng, n, 1000, 200);
            v = verify_and_fix(v);
            let t = rng.gen_range_i32(-1000, 1000);
            (v, t)
        }
    }
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (vals, target) = make_case(&mut rng, mode, t);
        // Final safety check
        let vals = verify_and_fix(vals);
        let target = if target < -1000 { -1000 } else if target > 1000 { 1000 } else { target };
        let (out, tgt) = generate_test_case(&vals, target);
        print_json(&out, tgt);
    }
}