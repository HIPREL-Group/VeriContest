use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    h_vals: &Vec<i32>,
    v_vals: &Vec<i32>,
) -> (result: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= m <= 20,
        1 <= n <= 20,
        h_vals.len() == m - 1,
        v_vals.len() == n - 1,
        forall |i: int| 0 <= i < h_vals.len() ==> 1 <= #[trigger] h_vals[i] <= 1000,
        forall |j: int| 0 <= j < v_vals.len() ==> 1 <= #[trigger] v_vals[j] <= 1000,
    ensures
        ({
            let (rm, rn, rh, rv) = result;
            &&& 1 <= rm <= 20
            &&& 1 <= rn <= 20
            &&& rh.len() == rm - 1
            &&& rv.len() == rn - 1
            &&& (forall |i: int| 0 <= i < rh.len() ==> 1 <= #[trigger] rh[i] <= 1000)
            &&& (forall |j: int| 0 <= j < rv.len() ==> 1 <= #[trigger] rv[j] <= 1000)
        }),
{
    let mut h_out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < h_vals.len()
        invariant
            0 <= i <= h_vals.len(),
            h_out.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] h_out[k] == h_vals[k],
            forall |k: int| 0 <= k < h_vals.len() ==> 1 <= #[trigger] h_vals[k] <= 1000,
        decreases h_vals.len() - i,
    {
        h_out.push(h_vals[i]);
        i += 1;
    }

    let mut v_out: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < v_vals.len()
        invariant
            0 <= j <= v_vals.len(),
            v_out.len() == j,
            forall |k: int| 0 <= k < j as int ==> #[trigger] v_out[k] == v_vals[k],
            forall |k: int| 0 <= k < v_vals.len() ==> 1 <= #[trigger] v_vals[k] <= 1000,
        decreases v_vals.len() - j,
    {
        v_out.push(v_vals[j]);
        j += 1;
    }

    assert(forall |k: int| 0 <= k < h_out.len() ==> #[trigger] h_out[k] == h_vals[k]);
    assert(forall |k: int| 0 <= k < v_out.len() ==> #[trigger] v_out[k] == v_vals[k]);

    (m, n, h_out, v_out)
}

}

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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn print_json(m: i32, n: i32, h: &[i32], v: &[i32]) {
    print!("{{\"m\":{},\"n\":{},\"horizontal_cut\":[", m, n);
    for (i, x) in h.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("{}", x);
    }
    print!("],\"vertical_cut\":[");
    for (i, x) in v.iter().enumerate() {
        if i > 0 { print!(","); }
        print!("{}", x);
    }
    println!("]}}");
}

fn build_vec(vals: Vec<i32>) -> Vec<i32> {
    vals
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // m=1, n=1 (empty arrays)
            (1, 1, Vec::new(), Vec::new())
        }
        1 => {
            // m=1, n=20
            let n = 20;
            let mut v = Vec::new();
            for _ in 0..(n - 1) { v.push(rng.gen_range_i32(1, 1000)); }
            (1, n, Vec::new(), v)
        }
        2 => {
            // m=20, n=1
            let m = 20;
            let mut h = Vec::new();
            for _ in 0..(m - 1) { h.push(rng.gen_range_i32(1, 1000)); }
            (m, 1, h, Vec::new())
        }
        3 => {
            // m=20, n=20 all max
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..19 { h.push(1000); v.push(1000); }
            (20, 20, h, v)
        }
        4 => {
            // all min (1)
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..19 { h.push(1); v.push(1); }
            (20, 20, h, v)
        }
        5 => {
            // horizontal dominates
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..19 { h.push(1000); v.push(1); }
            (20, 20, h, v)
        }
        6 => {
            // vertical dominates
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..19 { h.push(1); v.push(1000); }
            (20, 20, h, v)
        }
        7 => {
            // example 1
            (3, 2, vec![1, 3], vec![5])
        }
        8 => {
            // example 2
            (2, 2, vec![7], vec![4])
        }
        9 => {
            // random small
            let m = rng.gen_range_i32(1, 5);
            let n = rng.gen_range_i32(1, 5);
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..(m - 1) { h.push(rng.gen_range_i32(1, 1000)); }
            for _ in 0..(n - 1) { v.push(rng.gen_range_i32(1, 1000)); }
            (m, n, h, v)
        }
        _ => {
            // fully random
            let m = rng.gen_range_i32(1, 20);
            let n = rng.gen_range_i32(1, 20);
            let mut h = Vec::new();
            let mut v = Vec::new();
            for _ in 0..(m - 1) { h.push(rng.gen_range_i32(1, 1000)); }
            for _ in 0..(n - 1) { v.push(rng.gen_range_i32(1, 1000)); }
            let _ = t;
            let _ = rng.gen_range_usize(0, 1);
            (m, n, h, v)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 { args[1].parse().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200;
    let modes = 11;

    for t in 0..total {
        let mode = t % modes;
        let (m, n, h, v) = gen_mode(&mut rng, mode, t);
        let h = build_vec(h);
        let v = build_vec(v);
        let (rm, rn, rh, rv) = generate_test_case(m, n, &h, &v);
        print_json(rm, rn, &rh, &rv);
    }
}