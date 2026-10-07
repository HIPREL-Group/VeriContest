use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    extra: i32,
    fill: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= m <= 40_000,
        1 <= n <= 40_000,
        0 <= extra <= 100,
        1 <= fill <= 100_000,
        (m as int) * (n as int) + (extra as int) <= 50_000,
        (m as int) * (n as int) + (extra as int) >= 1,
    ensures
        1 <= res.0.len() <= 50_000,
        1 <= res.1 <= 40_000,
        1 <= res.2 <= 40_000,
        res.1 == m,
        res.2 == n,
        (res.1 as int) * (res.2 as int) <= usize::MAX,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100_000,
{
    let total: usize = (m as usize) * (n as usize) + (extra as usize);
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < total
        invariant
            0 <= i <= total,
            v.len() == i,
            1 <= fill <= 100_000,
            forall |k: int| 0 <= k < v.len() ==> 1 <= #[trigger] v[k] <= 100_000,
        decreases total - i,
    {
        v.push(fill);
        i = i + 1;
    }

    assert((m as int) * (n as int) <= 40_000int * 40_000int);
    assert((m as int) * (n as int) <= usize::MAX);

    (v, m, n)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_case(v: &[i32], m: i32, n: i32) {
    print!("{{\"original\":[");
    for i in 0..v.len() {
        if i > 0 { print!(","); }
        print!("{}", v[i]);
    }
    println!("],\"m\":{},\"n\":{}}}", m, n);
}

fn pick_case(mode: usize, rng: &mut Rng) -> (i32, i32, i32, i32) {
    // returns (m, n, extra, fill) with constraints:
    // 1<=m<=40000, 1<=n<=40000, 0<=extra<=100, 1<=fill<=100000, m*n+extra in [1,50000]
    match mode {
        0 => (1, 1, 0, 1),
        1 => (1, 1, 0, 100_000),
        2 => {
            // small random matching
            let m = rng.gen_range_i32(1, 10);
            let n = rng.gen_range_i32(1, 10);
            let fill = rng.gen_range_i32(1, 100_000);
            (m, n, 0, fill)
        }
        3 => {
            // mismatch: extra elements
            let m = rng.gen_range_i32(1, 20);
            let n = rng.gen_range_i32(1, 20);
            let extra = rng.gen_range_i32(1, 50);
            (m, n, extra, 1)
        }
        4 => {
            // single row
            let n = rng.gen_range_i32(1, 1000);
            (1, n, 0, 50_000)
        }
        5 => {
            // single col
            let m = rng.gen_range_i32(1, 1000);
            (m, 1, 0, 1)
        }
        6 => {
            // large exact
            (200, 250, 0, 42) // 50000
        }
        7 => {
            // large with mismatch
            (200, 249, 0, 7) // 49800
        }
        8 => {
            // m*n=1, extra>0 mismatch
            (1, 1, 10, 5)
        }
        9 => {
            let m = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_i32(1, 100);
            let prod = (m as i64) * (n as i64);
            if prod > 50_000 {
                (1, 1, 0, 1)
            } else {
                let max_extra = std::cmp::min(100, 50_000 - prod as i32);
                let extra = if max_extra <= 0 { 0 } else { rng.gen_range_i32(0, max_extra) };
                (m, n, extra, rng.gen_range_i32(1, 100_000))
            }
        }
        _ => {
            let m = rng.gen_range_i32(1, 50);
            let n = rng.gen_range_i32(1, 50);
            (m, n, 0, rng.gen_range_i32(1, 100_000))
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 { args[1].parse().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 10usize;
    for t in 0..total {
        let mode = t % modes;
        let (m, n, extra, fill) = pick_case(mode, &mut rng);
        // Sanity check bounds before calling verified function
        if m < 1 || m > 40_000 || n < 1 || n > 40_000 { continue; }
        if extra < 0 || extra > 100 { continue; }
        if fill < 1 || fill > 100_000 { continue; }
        let prod = (m as i64) * (n as i64) + (extra as i64);
        if prod < 1 || prod > 50_000 { continue; }

        let (v, mm, nn) = generate_test_case(m, n, extra, fill);
        print_case(&v, mm, nn);
    }
}