use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 1000,
        1 <= nums2.len() <= 1000,
        forall |i: int| 0 <= i < nums1.len() ==> -1000 <= #[trigger] nums1[i] <= 1000,
        forall |j: int| 0 <= j < nums2.len() ==> -1000 <= #[trigger] nums2[j] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall |j: int| 0 <= j < result.1.len() ==> -1000 <= #[trigger] result.1[j] <= 1000,
{
    (nums1, nums2)
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

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_i32(lo, hi));
    }
    v
}

fn clamp_len(n: usize) -> usize {
    if n < 1 {
        1
    } else if n > 1000 {
        1000
    } else {
        n
    }
}

fn clamp_val(v: i32) -> i32 {
    if v < -1000 {
        -1000
    } else if v > 1000 {
        1000
    } else {
        v
    }
}

fn sanitize(v: Vec<i32>) -> Vec<i32> {
    let mut out: Vec<i32> = Vec::with_capacity(v.len().max(1));
    for x in v.iter() {
        out.push(clamp_val(*x));
    }
    if out.is_empty() {
        out.push(0);
    }
    if out.len() > 1000 {
        out.truncate(1000);
    }
    out
}

fn pick_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // Small simple
            let a = vec![1, 2, 3];
            let b = vec![2, 4, 6];
            (a, b)
        }
        1 => {
            // Duplicates in both
            let a = vec![1, 2, 3, 3];
            let b = vec![1, 1, 2, 2];
            (a, b)
        }
        2 => {
            // Identical arrays
            let len = rng.gen_usize(1, 20);
            let v = build_vec(rng, len, -10, 10);
            (v.clone(), v)
        }
        3 => {
            // Disjoint arrays
            let la = rng.gen_usize(1, 30);
            let lb = rng.gen_usize(1, 30);
            let mut a = Vec::with_capacity(la);
            for _ in 0..la {
                a.push(rng.gen_i32(-1000, -1));
            }
            let mut b = Vec::with_capacity(lb);
            for _ in 0..lb {
                b.push(rng.gen_i32(1, 1000));
            }
            (a, b)
        }
        4 => {
            // Single elements
            let a = vec![rng.gen_i32(-1000, 1000)];
            let b = vec![rng.gen_i32(-1000, 1000)];
            (a, b)
        }
        5 => {
            // Max length both
            let a = build_vec(rng, 1000, -1000, 1000);
            let b = build_vec(rng, 1000, -1000, 1000);
            (a, b)
        }
        6 => {
            // All same value
            let va = rng.gen_i32(-1000, 1000);
            let vb = rng.gen_i32(-1000, 1000);
            let la = rng.gen_usize(1, 50);
            let lb = rng.gen_usize(1, 50);
            let a = vec![va; la];
            let b = vec![vb; lb];
            (a, b)
        }
        7 => {
            // Boundary values
            let a = vec![-1000, 1000, 0, -1000, 1000];
            let b = vec![1000, -1000, 0, 500, -500];
            (a, b)
        }
        8 => {
            // One subset of other
            let la = rng.gen_usize(2, 20);
            let a = build_vec(rng, la, -10, 10);
            let take = rng.gen_usize(1, la);
            let mut b = Vec::with_capacity(take);
            for i in 0..take {
                b.push(a[i]);
            }
            (a, b)
        }
        9 => {
            // Random mid
            let la_val = rng.gen_usize(1, 50);
            let lb_val = rng.gen_usize(1, 50);
            let a = build_vec(rng, la_val, -10, 10);
            let b = build_vec(rng, lb_val, -10, 10);
            (a, b)
        }
        _ => {
            // Mixed with big range
            let la = rng.gen_usize(10, 100);
            let lb = rng.gen_usize(10, 100);
            let big = build_vec(rng, la, -50, 50);
            let small = build_vec(rng, lb, -50, 50);
            (big, small)
        }
    }
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums2[i]);
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
        let (raw_a, raw_b) = pick_case(&mut rng, mode);

        let a = sanitize(raw_a);
        let b = sanitize(raw_b);

        // Ensure lengths valid (already handled but re-check)
        let mut a = a;
        let mut b = b;
        let la = clamp_len(a.len());
        let lb = clamp_len(b.len());
        a.truncate(la);
        b.truncate(lb);
        if a.is_empty() {
            a.push(0);
        }
        if b.is_empty() {
            b.push(0);
        }

        let (out_a, out_b) = generate_test_case(a, b);
        print_json(&out_a, &out_b);
    }
}