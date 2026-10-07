use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (pref: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000,
    ensures
        1 <= pref.len() <= 100_000,
        pref.len() == values.len(),
        forall |i: int| 0 <= i < pref.len() ==> 0 <= #[trigger] pref[i] <= 1_000_000,
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            result.len() == i,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] result[k] <= 1_000_000,
            forall |k: int| 0 <= k < i as int ==> result[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000,
        decreases values.len() - i,
    {
        result.push(values[i]);
        i = i + 1;
    }
    result
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

fn gen_mode(rng: &mut Rng, mode: usize, idx: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum size n=1
            let v = rng.gen_range_i32(0, 1_000_000);
            vec![v]
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(1, 50);
            vec![0i32; n]
        }
        2 => {
            // all same value
            let n = rng.gen_range_usize(2, 100);
            let v = rng.gen_range_i32(0, 1_000_000);
            vec![v; n]
        }
        3 => {
            // max size
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
        4 => {
            // all max
            let n = rng.gen_range_usize(1, 100);
            vec![1_000_000i32; n]
        }
        5 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
        6 => {
            // increasing
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) % 1_000_001);
            }
            v
        }
        7 => {
            // alternating 0 and value
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            let x = rng.gen_range_i32(0, 1_000_000);
            for i in 0..n {
                if i % 2 == 0 { v.push(0); } else { v.push(x); }
            }
            v
        }
        8 => {
            // powers of two pattern
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((1i32 << (i % 20)) & 0xFFFFF);
            }
            v
        }
        9 => {
            // n=2
            let a = rng.gen_range_i32(0, 1_000_000);
            let b = rng.gen_range_i32(0, 1_000_000);
            vec![a, b]
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
    };
    // unreachable fallback
    let _ = idx;
    let n = rng.gen_range_usize(1, 10);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(rng.gen_range_i32(0, 1_000_000)); }
    v
}

fn build_values(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            let v = rng.gen_range_i32(0, 1_000_000);
            vec![v]
        }
        1 => {
            let n = rng.gen_range_usize(1, 50);
            vec![0i32; n]
        }
        2 => {
            let n = rng.gen_range_usize(2, 100);
            let v = rng.gen_range_i32(0, 1_000_000);
            vec![v; n]
        }
        3 => {
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
        4 => {
            let n = rng.gen_range_usize(1, 100);
            vec![1_000_000i32; n]
        }
        5 => {
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
        6 => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) % 1_000_001);
            }
            v
        }
        7 => {
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            let x = rng.gen_range_i32(0, 1_000_000);
            for i in 0..n {
                if i % 2 == 0 { v.push(0); } else { v.push(x); }
            }
            v
        }
        8 => {
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let val = 1i32 << (i % 20);
                v.push(val & 0xFFFFF);
            }
            v
        }
        9 => {
            let a = rng.gen_range_i32(0, 1_000_000);
            let b = rng.gen_range_i32(0, 1_000_000);
            vec![a, b]
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            v
        }
    }
}

fn print_json(pref: &[i32]) {
    print!("{{\"pref\":[");
    for i in 0..pref.len() {
        if i > 0 { print!(","); }
        print!("{}", pref[i]);
    }
    println!("]}}");
}

fn main() {
    // suppress unused warning for gen_mode
    let _ = gen_mode;

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
        let values = build_values(&mut rng, mode);
        let pref = generate_test_case(&values);
        print_json(&pref);
    }
}