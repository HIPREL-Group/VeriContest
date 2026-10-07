use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base: i32,
    deltas: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= deltas.len() <= 30_000,
        -10_000 <= base <= 10_000,
        forall |i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        forall |i: int| 0 <= i < deltas.len() ==> (#[trigger] deltas[i]) as int + base as int <= 10_000,
        forall |i: int, j: int| 0 <= i <= j < deltas.len() ==> deltas[i] <= deltas[j],
    ensures
        1 <= nums.len() <= 30_000,
        nums.len() == deltas.len(),
        forall |i: int| 0 <= i < nums.len() ==>
            -10_000 <= #[trigger] nums[i] <= 10_000,
        forall |i: int, j: int| 0 <= i <= j < nums.len() ==>
            nums[i] <= nums[j],
{
    let n = deltas.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == deltas.len(),
            1 <= n <= 30_000,
            0 <= pos <= n,
            nums.len() == pos,
            -10_000 <= base <= 10_000,
            forall |i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
            forall |i: int| 0 <= i < deltas.len() ==> (#[trigger] deltas[i]) as int + base as int <= 10_000,
            forall |i: int, j: int| 0 <= i <= j < deltas.len() ==> deltas[i] <= deltas[j],
            forall |k: int| 0 <= k < pos as int ==>
                #[trigger] nums[k] as int == base as int + deltas[k] as int,
            forall |k: int| 0 <= k < pos as int ==>
                -10_000 <= #[trigger] nums[k] <= 10_000,
        decreases n - pos,
    {
        let v: i32 = base + deltas[pos];
        nums.push(v);
        pos = pos + 1;
    }

    assert forall |i: int, j: int| 0 <= i <= j < nums.len() implies nums[i] <= nums[j] by {
        assert(nums[i] as int == base as int + deltas[i] as int);
        assert(nums[j] as int == base as int + deltas[j] as int);
        assert(deltas[i] <= deltas[j]);
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

fn make_sorted_deltas(rng: &mut Rng, n: usize, max_delta: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(0, max_delta));
    }
    v.sort();
    v
}

fn clamp_base(base: i32, deltas: &Vec<i32>) -> i32 {
    // ensure base + max_delta <= 10_000 and base >= -10_000
    let max_d = *deltas.iter().max().unwrap_or(&0);
    let mut b = base;
    if b > 10_000 - max_d {
        b = 10_000 - max_d;
    }
    if b < -10_000 {
        b = -10_000;
    }
    b
}

fn mode_generate(rng: &mut Rng, mode: usize) -> (i32, Vec<i32>) {
    match mode {
        0 => {
            // single element
            let d = vec![rng.gen_range_i32(0, 100)];
            let base = rng.gen_range_i32(-10_000, 10_000 - 100);
            (base, d)
        }
        1 => {
            // all same value
            let n = rng.gen_range_usize(1, 50);
            let base = rng.gen_range_i32(-10_000, 10_000);
            let mut d = Vec::new();
            for _ in 0..n { d.push(0); }
            (base, d)
        }
        2 => {
            // exactly two duplicates per value
            let n = rng.gen_range_usize(1, 100);
            let mut d = Vec::new();
            let mut cur: i32 = 0;
            while d.len() < n {
                d.push(cur);
                if d.len() < n { d.push(cur); }
                cur += 1;
            }
            let base = rng.gen_range_i32(-10_000, 10_000 - cur);
            (base, d)
        }
        3 => {
            // three duplicates per value
            let n = rng.gen_range_usize(3, 60);
            let mut d = Vec::new();
            let mut cur: i32 = 0;
            while d.len() < n {
                for _ in 0..3 {
                    if d.len() < n { d.push(cur); }
                }
                cur += 1;
            }
            let base = clamp_base(rng.gen_range_i32(-10_000, 10_000), &d);
            (base, d)
        }
        4 => {
            // many duplicates of first element
            let n = rng.gen_range_usize(5, 200);
            let k = rng.gen_range_usize(2, n);
            let mut d = Vec::new();
            for _ in 0..k { d.push(0); }
            let mut c: i32 = 1;
            while d.len() < n {
                d.push(c);
                c += 1;
            }
            let base = clamp_base(-5_000, &d);
            (base, d)
        }
        5 => {
            // all distinct
            let n = rng.gen_range_usize(1, 200);
            let mut d = Vec::new();
            for i in 0..n {
                d.push(i as i32);
            }
            let base = clamp_base(-100, &d);
            (base, d)
        }
        6 => {
            // max size, alternating duplicates
            let n = 30_000;
            let mut d: Vec<i32> = Vec::with_capacity(n);
            let mut cur: i32 = 0;
            while d.len() < n {
                d.push(cur);
                if d.len() < n { d.push(cur); }
                cur += 1;
                if cur > 15_000 { cur = 15_000; }
            }
            let base = clamp_base(-10_000, &d);
            (base, d)
        }
        7 => {
            // random sorted
            let n = rng.gen_range_usize(1, 500);
            let max_d = rng.gen_range_i32(1, 200);
            let d = make_sorted_deltas(rng, n, max_d);
            let base = clamp_base(rng.gen_range_i32(-10_000, 10_000), &d);
            (base, d)
        }
        8 => {
            // heavy duplicates (4+)
            let n = rng.gen_range_usize(4, 80);
            let mut d = Vec::new();
            let mut cur: i32 = 0;
            while d.len() < n {
                let reps = rng.gen_range_usize(1, 5);
                for _ in 0..reps {
                    if d.len() < n { d.push(cur); }
                }
                cur += 1;
            }
            let base = clamp_base(rng.gen_range_i32(-10_000, 10_000), &d);
            (base, d)
        }
        9 => {
            // two elements
            let d: Vec<i32> = vec![0, 0];
            let base = rng.gen_range_i32(-10_000, 10_000);
            (base, d)
        }
        _ => {
            // negative-heavy random
            let n = rng.gen_range_usize(1, 300);
            let d = make_sorted_deltas(rng, n, 50);
            (clamp_base(-10_000, &d), d)
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
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
        let (base, deltas) = mode_generate(&mut rng, mode);
        // validate invariants defensively
        if deltas.is_empty() { continue; }
        if deltas.len() > 30_000 { continue; }
        let mut ok = true;
        let mut prev: i32 = -1;
        for &x in &deltas {
            if x < 0 { ok = false; break; }
            if x < prev { ok = false; break; }
            if (base as i64) + (x as i64) > 10_000 { ok = false; break; }
            if (base as i64) + (x as i64) < -10_000 { ok = false; break; }
            prev = x;
        }
        if base < -10_000 || base > 10_000 { ok = false; }
        if !ok { continue; }

        let nums = generate_test_case(base, &deltas);
        print_json(&nums);
    }
}