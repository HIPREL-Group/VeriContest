use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    heights_in: Vec<i32>,
    k: usize,
) -> (result: (Vec<i32>, usize))
    requires
        heights_in.len() >= 1,
        heights_in.len() <= 150_000,
        1 <= k <= heights_in.len(),
        forall |i: int| 0 <= i < heights_in.len() ==> 1 <= #[trigger] heights_in@[i] <= 100,
    ensures
        result.0.len() == heights_in.len(),
        result.0.len() <= 150_000,
        1 <= result.1 <= result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
{
    (heights_in, k)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_heights(vals: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::with_capacity(vals.len());
    for v in vals {
        let mut vv = v;
        if vv < 1 { vv = 1; }
        if vv > 100 { vv = 100; }
        out.push(vv);
    }
    out
}

fn print_json(heights: &[i32], k: usize) {
    print!("{{\"heights\":[");
    for i in 0..heights.len() {
        if i > 0 { print!(","); }
        print!("{}", heights[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn gen_case(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, usize) {
    match mode {
        0 => {
            // tiny
            let n = rng.gen_range_usize(1, 5);
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), k)
        }
        1 => {
            // n==k
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), n)
        }
        2 => {
            // k==1
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), 1)
        }
        3 => {
            // all equal
            let n = rng.gen_range_usize(1, 200);
            let k = rng.gen_range_usize(1, n);
            let x = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            (build_heights(v), k)
        }
        4 => {
            // min at beginning
            let n = rng.gen_range_usize(3, 200);
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for i in 0..n {
                if i < k { v.push(1); } else { v.push(rng.gen_range_i32(50, 100)); }
            }
            (build_heights(v), k)
        }
        5 => {
            // min at end
            let n = rng.gen_range_usize(3, 200);
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for i in 0..n {
                if i >= n - k { v.push(1); } else { v.push(rng.gen_range_i32(50, 100)); }
            }
            (build_heights(v), k)
        }
        6 => {
            // min in middle
            let n = rng.gen_range_usize(5, 300);
            let k = rng.gen_range_usize(1, n);
            let start = (n - k) / 2;
            let mut v = Vec::new();
            for i in 0..n {
                if i >= start && i < start + k { v.push(1); } else { v.push(rng.gen_range_i32(50, 100)); }
            }
            (build_heights(v), k)
        }
        7 => {
            // multiple minimum windows (tie-breaking - first one)
            let n = rng.gen_range_usize(4, 200);
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
            (build_heights(v), k)
        }
        8 => {
            // large n
            let n = 150_000;
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), k)
        }
        9 => {
            // large n, k near n
            let n = 150_000;
            let k = n - (idx % 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), k)
        }
        _ => {
            // random general
            let n = rng.gen_range_usize(1, 1000);
            let k = rng.gen_range_usize(1, n);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            (build_heights(v), k)
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (heights, k) = gen_case(&mut rng, mode, t);
        // Validate bounds
        if heights.len() == 0 || heights.len() > 150_000 { continue; }
        if k < 1 || k > heights.len() { continue; }
        let mut ok = true;
        for &h in &heights {
            if h < 1 || h > 100 { ok = false; break; }
        }
        if !ok { continue; }
        let (h2, k2) = generate_test_case(heights, k);
        print_json(&h2, k2);
    }
}