use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    xs: Vec<i64>,
    ps: Vec<i64>,
) -> (res: (Vec<i64>, Vec<i64>))
    requires
        2 <= xs.len() <= 300_000,
        1 <= ps.len() <= 300_000,
        forall|k: int| 0 <= k < xs.len() - 1 ==> #[trigger] xs[k] < xs[k + 1],
        forall|k: int| 0 <= k < xs.len() ==> 1 <= #[trigger] xs[k] <= 1_000_000_000_000_000_000,
        forall|k: int| 0 <= k < ps.len() ==> 1 <= #[trigger] ps[k] <= 1_000_000_000_000_000_000,
    ensures
        2 <= res.0.len() <= 300_000,
        1 <= res.1.len() <= 300_000,
        forall|k: int| 0 <= k < res.0.len() - 1 ==> #[trigger] res.0[k] < res.0[k + 1],
        forall|k: int| 0 <= k < res.0.len() ==> 1 <= #[trigger] res.0[k] <= 1_000_000_000_000_000_000,
        forall|k: int| 0 <= k < res.1.len() ==> 1 <= #[trigger] res.1[k] <= 1_000_000_000_000_000_000,
{
    (xs, ps)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128 ^ ((self.next_u64() as u128) << 32)) % span;
        lo + v as i64
    }
}

fn build_arith(n: usize, start: i64, step: i64) -> Vec<i64> {
    let mut v = Vec::with_capacity(n);
    let mut cur = start;
    for _ in 0..n {
        v.push(cur);
        cur += step;
    }
    v
}

fn build_increasing_random(rng: &mut Rng, n: usize, max_step: i64) -> Vec<i64> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i64 = rng.gen_range_i64(1, 100);
    v.push(cur);
    for _ in 1..n {
        let s = rng.gen_range_i64(1, max_step.max(1));
        cur = cur.saturating_add(s);
        if cur > 1_000_000_000_000_000_000 {
            cur = 1_000_000_000_000_000_000 - (n as i64);
        }
        v.push(cur);
    }
    // Ensure strictly increasing and in bounds
    for i in 1..n {
        if v[i] <= v[i-1] {
            v[i] = v[i-1] + 1;
        }
        if v[i] > 1_000_000_000_000_000_000 {
            v[i] = 1_000_000_000_000_000_000;
        }
    }
    // May break monotonicity at top; fix by clamping from end
    for i in (1..n).rev() {
        if v[i] <= v[i-1] {
            if v[i-1] > 1 {
                v[i-1] = v[i] - 1;
            }
        }
    }
    // Ensure first >= 1
    if v[0] < 1 { v[0] = 1; }
    for i in 1..n {
        if v[i] <= v[i-1] { v[i] = v[i-1] + 1; }
    }
    v
}

fn gen_ps(rng: &mut Rng, m: usize, include: Option<i64>) -> Vec<i64> {
    let mut v = Vec::with_capacity(m);
    for _ in 0..m {
        v.push(rng.gen_range_i64(1, 1_000_000_000_000_000_000));
    }
    if let Some(p) = include {
        let idx = rng.gen_range_usize(0, m - 1);
        v[idx] = p.max(1).min(1_000_000_000_000_000_000);
    }
    v
}

fn print_json(xs: &[i64], ps: &[i64]) {
    print!("{{\"a\":[");
    for i in 0..xs.len() {
        if i > 0 { print!(","); }
        print!("{}", xs[i]);
    }
    print!("],\"b\":[");
    for i in 0..ps.len() {
        if i > 0 { print!(","); }
        print!("{}", ps[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200;
    for t in 0..total {
        let mode = t % 10;
        let (xs, ps) = match mode {
            0 => {
                // small arithmetic with matching p
                let n = rng.gen_range_usize(2, 10);
                let start = rng.gen_range_i64(1, 100);
                let step = rng.gen_range_i64(1, 20);
                let xs = build_arith(n, start, step);
                let m = rng.gen_range_usize(1, 10);
                let ps = gen_ps(&mut rng, m, Some(step));
                (xs, ps)
            }
            1 => {
                // no matching p (random)
                let n = rng.gen_range_usize(2, 20);
                let xs = build_increasing_random(&mut rng, n, 1_000_000);
                let m = rng.gen_range_usize(1, 10);
                let ps = gen_ps(&mut rng, m, None);
                (xs, ps)
            }
            2 => {
                // large n
                let n = 100_000;
                let step: i64 = 7;
                let xs = build_arith(n, 1, step);
                let m = 5;
                let ps = gen_ps(&mut rng, m, Some(step));
                (xs, ps)
            }
            3 => {
                // max xi
                let n = rng.gen_range_usize(2, 5);
                let step: i64 = 1_000_000_000;
                let xs = build_arith(n, 1, step);
                let m = rng.gen_range_usize(1, 5);
                let ps = gen_ps(&mut rng, m, Some(step));
                (xs, ps)
            }
            4 => {
                // n=2 minimum
                let a = rng.gen_range_i64(1, 500_000_000_000_000_000);
                let b = a + rng.gen_range_i64(1, 500_000_000_000_000_000);
                let xs = vec![a, b];
                let m = 1;
                let ps = vec![b - a];
                (xs, ps)
            }
            5 => {
                // m=1, wrong p
                let n = rng.gen_range_usize(2, 50);
                let xs = build_arith(n, 1, 6);
                let ps = vec![5i64];
                (xs, ps)
            }
            6 => {
                // step=1
                let n = rng.gen_range_usize(2, 100);
                let xs = build_arith(n, 1, 1);
                let m = rng.gen_range_usize(1, 10);
                let ps = gen_ps(&mut rng, m, Some(1));
                (xs, ps)
            }
            7 => {
                // multiple divisors
                let n = rng.gen_range_usize(2, 30);
                let step: i64 = 12;
                let xs = build_arith(n, 5, step);
                let mut ps = vec![1i64, 2, 3, 4, 6, 12, 7];
                while ps.len() > rng.gen_range_usize(1, 7) { ps.pop(); }
                if ps.is_empty() { ps.push(1); }
                (xs, ps)
            }
            8 => {
                // random increasing with divisor in p
                let n = rng.gen_range_usize(2, 50);
                let xs = build_increasing_random(&mut rng, n, 100);
                let m = rng.gen_range_usize(1, 10);
                let ps = gen_ps(&mut rng, m, Some(1));
                (xs, ps)
            }
            _ => {
                // large m
                let n = rng.gen_range_usize(2, 10);
                let step: i64 = 100;
                let xs = build_arith(n, 50, step);
                let m = 1000;
                let ps = gen_ps(&mut rng, m, Some(50));
                (xs, ps)
            }
        };

        // Verify preconditions before calling
        if xs.len() < 2 || xs.len() > 300_000 { continue; }
        if ps.is_empty() || ps.len() > 300_000 { continue; }
        let mut ok = true;
        for i in 0..xs.len() {
            if xs[i] < 1 || xs[i] > 1_000_000_000_000_000_000 { ok = false; break; }
            if i + 1 < xs.len() && xs[i] >= xs[i+1] { ok = false; break; }
        }
        if !ok { continue; }
        for i in 0..ps.len() {
            if ps[i] < 1 || ps[i] > 1_000_000_000_000_000_000 { ok = false; break; }
        }
        if !ok { continue; }

        let (xs2, ps2) = generate_test_case(xs, ps);
        print_json(&xs2, &ps2);
    }
}