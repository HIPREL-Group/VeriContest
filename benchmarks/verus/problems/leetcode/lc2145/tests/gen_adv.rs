use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    diffs: &Vec<i32>,
    lower: i32,
    upper: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= diffs.len() <= 100_000,
        -100_000 <= lower <= upper <= 100_000,
        forall |i: int| 0 <= i < diffs.len() ==> -100_000 <= #[trigger] diffs[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        -100_000 <= result.1 <= result.2 <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> -100_000 <= #[trigger] result.0[i] <= 100_000,
        result.1 == lower,
        result.2 == upper,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < diffs.len()
        invariant
            0 <= i <= diffs.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> -100_000 <= #[trigger] out[k] <= 100_000,
            forall |k: int| 0 <= k < i as int ==> out[k] == diffs[k],
            forall |k: int| 0 <= k < diffs.len() ==> -100_000 <= #[trigger] diffs[k] <= 100_000,
        decreases diffs.len() - i,
    {
        out.push(diffs[i]);
        i = i + 1;
    }
    (out, lower, upper)
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

fn clamp_diffs(v: &mut Vec<i32>) {
    for x in v.iter_mut() {
        if *x > 100_000 {
            *x = 100_000;
        }
        if *x < -100_000 {
            *x = -100_000;
        }
    }
}

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-10, 10));
            }
            let lower = rng.gen_range_i32(-20, 20);
            let upper = lower + rng.gen_range_i32(0, 40);
            (d, lower, upper.min(100_000))
        }
        1 => {
            // n=1
            let d = vec![rng.gen_range_i32(-100_000, 100_000)];
            let lower = rng.gen_range_i32(-100_000, 100_000);
            let upper_span = rng.gen_range_i32(0, 100_000);
            let upper = ((lower as i64) + (upper_span as i64)).min(100_000) as i32;
            (d, lower, upper)
        }
        2 => {
            // max size n=100000
            let n = 100_000usize;
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-100_000, 100_000));
            }
            let lower = rng.gen_range_i32(-100_000, 100_000);
            let upper_span = rng.gen_range_i32(0, 100_000);
            let upper = ((lower as i64) + (upper_span as i64)).min(100_000) as i32;
            (d, lower, upper)
        }
        3 => {
            // all zeros
            let n = rng.gen_range_usize(1, 1000);
            let d = vec![0i32; n];
            let lower = rng.gen_range_i32(-100_000, 100_000);
            let upper_span = rng.gen_range_i32(0, 100_000);
            let upper = ((lower as i64) + (upper_span as i64)).min(100_000) as i32;
            (d, lower, upper)
        }
        4 => {
            // lower == upper
            let n = rng.gen_range_usize(1, 100);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-5, 5));
            }
            let lower = rng.gen_range_i32(-100, 100);
            (d, lower, lower)
        }
        5 => {
            // extreme values
            let n = rng.gen_range_usize(1, 100);
            let mut d = Vec::with_capacity(n);
            for i in 0..n {
                d.push(if i % 2 == 0 { 100_000 } else { -100_000 });
            }
            (d, -100_000, 100_000)
        }
        6 => {
            // range too tight - likely zero answer
            let n = rng.gen_range_usize(1, 50);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-100_000, 100_000));
            }
            let x = rng.gen_range_i32(-100_000, 100_000);
            (d, x, x)
        }
        7 => {
            // monotonic increasing
            let n = rng.gen_range_usize(2, 200);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(1, 100));
            }
            let lower = -100_000;
            let upper = 100_000;
            (d, lower, upper)
        }
        8 => {
            // monotonic decreasing
            let n = rng.gen_range_usize(2, 200);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-100, -1));
            }
            (d, -100_000, 100_000)
        }
        9 => {
            // near-boundary lower=-100000,upper=100000
            let n = rng.gen_range_usize(1, 10_000);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-100_000, 100_000));
            }
            (d, -100_000, 100_000)
        }
        _ => {
            let n = rng.gen_range_usize(1, 500);
            let mut d = Vec::with_capacity(n);
            for _ in 0..n {
                d.push(rng.gen_range_i32(-1000, 1000));
            }
            let lower = rng.gen_range_i32(-10_000, 10_000);
            let upper_span = rng.gen_range_i32(0, 20_000);
            let upper = ((lower as i64) + (upper_span as i64)).min(100_000) as i32;
            (d, lower, upper)
        }
    }
}

fn print_json(diffs: &[i32], lower: i32, upper: i32) {
    print!("{{\"differences\":[");
    for i in 0..diffs.len() {
        if i > 0 { print!(","); }
        print!("{}", diffs[i]);
    }
    println!("],\"lower\":{},\"upper\":{}}}", lower, upper);
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
        let (mut d, lower, upper) = make_test(&mut rng, mode);
        clamp_diffs(&mut d);
        if d.is_empty() {
            d.push(0);
        }
        if d.len() > 100_000 {
            d.truncate(100_000);
        }
        let lo = lower.max(-100_000).min(100_000);
        let up = upper.max(lo).min(100_000);
        let (out_d, out_lo, out_up) = generate_test_case(&d, lo, up);
        print_json(&out_d, out_lo, out_up);
    }
}