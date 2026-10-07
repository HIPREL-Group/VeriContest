use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (res: Vec<i32>)
    requires
        1 <= vals.len() <= 5_000,
        forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1_000,
    ensures
        1 <= res.len() <= 5_000,
        forall |i: int| 0 <= i < res.len() ==> 0 <= #[trigger] res[i] <= 1_000,
{
    let mut out: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 5_000,
            0 <= i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 1_000,
            forall |k: int| 0 <= k < out.len() ==> 0 <= #[trigger] out[k] <= 1_000,
        decreases n - i,
    {
        let v = vals[i];
        assert(0 <= v <= 1_000);
        out.push(v);
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => {
            // single element small
            let n = 1;
            let mut v = Vec::new();
            v.push(rng.gen_range_i32(0, 1000));
            let _ = n;
            v
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(0); }
            v
        }
        2 => {
            // all same, large
            let n = rng.gen_range_usize(1, 200);
            let x = rng.gen_range_i32(0, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        3 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 300);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((i as i32) * 1000 / (n as i32).max(1)).min(1000));
            }
            v
        }
        4 => {
            // sorted descending
            let n = rng.gen_range_usize(1, 300);
            let mut v = Vec::new();
            for i in 0..n {
                let val = 1000 - ((i as i32) * 1000 / (n as i32).max(1));
                v.push(val.max(0));
            }
            v
        }
        5 => {
            // max size
            let n = 5000;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1000)); }
            v
        }
        6 => {
            // h = n scenario: all large
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(n as i32, 1000)); }
            v
        }
        7 => {
            // 0 or 1000
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(0); } else { v.push(1000); }
            }
            v
        }
        8 => {
            // small values, h=0 likely
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(0); }
            if n > 0 { v[0] = rng.gen_range_i32(0, 5); }
            v
        }
        9 => {
            // n=5000 all equal edge
            let n = 5000;
            let x = rng.gen_range_i32(0, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1000)); }
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"citations\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let vals = build(mode, &mut rng);
        let out = generate_test_case(&vals);
        print_json(&out);
    }
}