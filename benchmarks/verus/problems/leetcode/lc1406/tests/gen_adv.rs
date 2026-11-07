use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 50_000,
        forall |i: int| 0 <= i < values.len() ==>
            -1000 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= result.len() <= 50_000,
        forall |i: int| 0 <= i < result.len() ==>
            -1000 <= #[trigger] result[i] <= 1000,
{
    let n = values.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] out[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==>
                -1000 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        out.push(values[i]);
        i = i + 1;
    }
    out
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vec(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Very small
            let n = rng.gen_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(-1000, 1000)); }
            v
        }
        1 => {
            // All positives
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(1, 1000)); }
            v
        }
        2 => {
            // All negatives
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(-1000, -1)); }
            v
        }
        3 => {
            // All zeros
            let n = rng.gen_usize(1, 100);
            vec![0i32; n]
        }
        4 => {
            // Extreme values
            let n = rng.gen_usize(2, 50);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1000 } else { -1000 });
            }
            v
        }
        5 => {
            // Max size
            let n = 50_000usize;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(-1000, 1000)); }
            v
        }
        6 => {
            // Near max size all 1000
            let n = 49_999usize;
            vec![1000i32; n]
        }
        7 => {
            // Examples
            let ex = [
                vec![1,2,3,7],
                vec![1,2,3,-9],
                vec![1,2,3,6],
                vec![-1,-2,-3],
                vec![1],
                vec![-1],
                vec![0],
                vec![1,2],
                vec![1,2,3],
                vec![7,7,7,7,7,7,7],
            ];
            ex[t % ex.len()].clone()
        }
        8 => {
            // Length multiple-of-3 boundary tests
            let ns = [3usize, 6, 9, 4, 5, 7, 8, 10, 11, 12];
            let n = ns[t % ns.len()];
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(-1000, 1000)); }
            v
        }
        9 => {
            // Alternating extremes, medium length
            let n = rng.gen_usize(100, 1000);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(match i % 4 {
                    0 => 1000,
                    1 => -1000,
                    2 => 0,
                    _ => rng.gen_i32(-1000, 1000),
                });
            }
            v
        }
        _ => {
            // Random medium
            let n = rng.gen_usize(50, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(-1000, 1000)); }
            v
        }
    }
}

fn print_json(v: &[i32]) {
    print!("{{\"stone_value\":[");
    for i in 0..v.len() {
        if i > 0 { print!(","); }
        print!("{}", v[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let v = build_vec(mode, &mut rng, t);
        // Ensure constraints
        assert!(v.len() >= 1 && v.len() <= 50_000);
        for &x in &v { assert!(x >= -1000 && x <= 1000); }
        let out = generate_test_case(&v);
        print_json(&out);
    }
}