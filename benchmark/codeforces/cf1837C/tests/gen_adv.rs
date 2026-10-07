use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i64>) -> (result: Vec<i64>)
    requires
        vals.len() >= 1,
        vals.len() <= 300_000,
        forall|i: int| 0 <= i < vals.len() ==> (#[trigger] vals@[i] == 0 || vals@[i] == 1 || vals@[i] == 2),
    ensures
        result.len() == vals.len(),
        result.len() >= 1,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1 || result@[i] == 2),
{
    let mut out: Vec<i64> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] out@[k] == vals@[k]),
            forall|k: int| 0 <= k < vals.len() ==> (#[trigger] vals@[k] == 0 || vals@[k] == 1 || vals@[k] == 2),
        decreases n - i,
    {
        out.push(vals[i]);
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i64> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range(1, 20),
        3 => rng.gen_range(1, 100),
        4 => rng.gen_range(100, 1000),
        5 => rng.gen_range(1, 50),
        6 => rng.gen_range(1, 50),
        7 => rng.gen_range(1, 50),
        8 => rng.gen_range(1, 50),
        9 => rng.gen_range(1, 1000),
        _ => rng.gen_range(1, 100),
    };

    let mut v: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            for _ in 0..n {
                v.push((rng.gen_range(0, 2)) as i64);
            }
        }
        5 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        6 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        7 => {
            // all ?
            for _ in 0..n { v.push(2); }
        }
        8 => {
            // alternating
            for i in 0..n {
                v.push(((i + t) % 3) as i64);
            }
        }
        9 => {
            // mostly ?
            for _ in 0..n {
                let r = rng.gen_range(0, 9);
                if r < 7 { v.push(2); }
                else if r == 7 { v.push(0); }
                else { v.push(1); }
            }
        }
        _ => {
            for _ in 0..n {
                v.push((rng.gen_range(0, 2)) as i64);
            }
        }
    }
    v
}

fn print_json(s: &[i64]) {
    print!("{{\"s\":[");
    for i in 0..s.len() {
        if i > 0 { print!(","); }
        print!("{}", s[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let vals = gen_mode(&mut rng, mode, t);
        let out = generate_test_case(&vals);
        print_json(&out);
    }
}