use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    bit: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= fillers.len() <= 100000,
        0 <= bit < 31,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10_000_000,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 < 31,
        result.1 == bit,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10_000_000,
{
    let n = fillers.len();
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            v.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 10_000_000,
            forall |k: int| 0 <= k < v.len() ==> 1 <= #[trigger] v[k] <= 10_000_000,
            forall |k: int| 0 <= k < v.len() ==> v[k] == fillers[k],
        decreases n - i,
    {
        v.push(fillers[i]);
        i = i + 1;
    }
    (v, bit)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    let n: usize = match mode {
        0 => 1,
        1 => 2 + (t % 10),
        2 => 100,
        3 => 1000,
        4 => 100000,
        5 => 50000,
        6 => rng.gen_range_usize(1, 500),
        7 => rng.gen_range_usize(1, 5000),
        8 => rng.gen_range_usize(1, 100),
        9 => 10,
        _ => rng.gen_range_usize(1, 1000),
    };

    let bit: i32 = match mode {
        0 => 0,
        1 => (t as i32) % 31,
        2 => 30,
        3 => 23, // ~10^7 is about 2^23.25
        4 => rng.gen_range_i32(0, 30),
        5 => rng.gen_range_i32(20, 30),
        6 => rng.gen_range_i32(0, 10),
        7 => rng.gen_range_i32(0, 23),
        8 => 23,
        9 => rng.gen_range_i32(0, 30),
        _ => rng.gen_range_i32(0, 30),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            v.push(1);
        }
        1 => {
            // all equal powers of two <= 10^7
            let powers: [i32; 24] = [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608];
            let p = powers[(t % 24) as usize];
            for _ in 0..n { v.push(p); }
        }
        2 => {
            // half have bit set, half don't
            for i in 0..n {
                if i % 2 == 0 {
                    let val = 1i32 << (bit.min(23));
                    v.push(if val >= 1 && val <= 10_000_000 { val } else { 1 });
                } else {
                    v.push(1);
                }
            }
        }
        3 => {
            // all 10^7
            for _ in 0..n { v.push(10_000_000); }
        }
        4 => {
            // max size random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000_000));
            }
        }
        5 => {
            // all share a specific bit
            let b = bit.min(23);
            let mask = 1i32 << b;
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 10_000_000);
                let val = (r | mask).min(10_000_000).max(1);
                v.push(val);
            }
        }
        6 => {
            // small values 1..100
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        7 => {
            // values around powers of two
            for _ in 0..n {
                let p = rng.gen_range_i32(0, 23);
                let base = 1i32 << p;
                let delta = rng.gen_range_i32(-2, 2);
                let val = (base + delta).max(1).min(10_000_000);
                v.push(val);
            }
        }
        8 => {
            // all 1s - only bit 0 set
            for _ in 0..n { v.push(1); }
        }
        9 => {
            // alternating high and low
            for i in 0..n {
                if i % 2 == 0 { v.push(10_000_000); } else { v.push(1); }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10_000_000));
            }
        }
    }

    // Safety: ensure all values are in range [1, 10_000_000]
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 10_000_000 { *x = 10_000_000; }
    }
    if v.is_empty() {
        v.push(1);
    }
    if v.len() > 100000 {
        v.truncate(100000);
    }

    let mut b = bit;
    if b < 0 { b = 0; }
    if b > 30 { b = 30; }

    (v, b)
}

fn print_json(candidates: &[i32], bit: i32) {
    print!("{{\"candidates\":[");
    for i in 0..candidates.len() {
        if i > 0 { print!(","); }
        print!("{}", candidates[i]);
    }
    println!("],\"bit\":{}}}", bit);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (fillers, bit) = build_mode(&mut rng, mode, t);
        let (v, b) = generate_test_case(&fillers, bit);
        print_json(&v, b);
    }
}