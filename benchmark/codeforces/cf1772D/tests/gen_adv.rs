use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (a: Vec<i32>)
    requires
        2 <= vals.len() <= 200000,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1000000000,
    ensures
        2 <= a.len() <= 200000,
        forall|i: int| 0 <= i < a.len() as int ==> 0 <= #[trigger] a[i] <= 1000000000,
{
    let n = vals.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            2 <= n <= 200000,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 1000000000,
            forall|k: int| 0 <= k < i as int ==> a[k] == vals[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] a[k] <= 1000000000,
        decreases n - i,
    {
        a.push(vals[i]);
        i = i + 1;
    }
    a
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
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            let n = 2 + (t % 5);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000_000)); }
            v
        }
        1 => {
            // sorted ascending
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000_000)); }
            v.sort();
            v
        }
        2 => {
            // sorted descending
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000_000)); }
            v.sort();
            v.reverse();
            v
        }
        3 => {
            // all same
            let n = rng.gen_range_usize(2, 100);
            let x = rng.gen_range_i32(0, 1_000_000_000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            v
        }
        4 => {
            // all zero
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(0); }
            v
        }
        5 => {
            // extremes
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                let p = rng.next_u64() % 3;
                let x = match p { 0 => 0, 1 => 1_000_000_000, _ => rng.gen_range_i32(0, 1_000_000_000) };
                v.push(x);
            }
            v
        }
        6 => {
            // large size
            let n = 200000;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000_000)); }
            v
        }
        7 => {
            // n=2 edge
            let a = rng.gen_range_i32(0, 1_000_000_000);
            let b = rng.gen_range_i32(0, 1_000_000_000);
            vec![a, b]
        }
        8 => {
            // small values
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 10)); }
            v
        }
        9 => {
            // alternating small/large
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 1_000_000_000 });
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(2, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000_000)); }
            v
        }
    }
}

fn print_json(a: &[i32]) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let vals = build_mode(&mut rng, mode, t);
        let a = generate_test_case(&vals);
        print_json(&a);
    }
}