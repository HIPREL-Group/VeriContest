use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 500,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000,
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000,
{
    let n = values.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 500,
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] result[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] result[k] <= 1_000_000,
        decreases n - i,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 500,
        4 => 500,
        5 => rng.gen_range_usize(1, 10),
        6 => rng.gen_range_usize(50, 150),
        7 => rng.gen_range_usize(1, 500),
        8 => 500,
        9 => rng.gen_range_usize(2, 20),
        _ => rng.gen_range_usize(1, 500),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { v.push(rng.gen_range_i32(1, 1_000_000)); }
        1 => {
            v.push(rng.gen_range_i32(1, 1_000_000));
            v.push(rng.gen_range_i32(1, 1_000_000));
        }
        2 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
        }
        3 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        4 => {
            // all max
            for _ in 0..n { v.push(1_000_000); }
        }
        5 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
        }
        6 => {
            // all same
            let x = rng.gen_range_i32(1, 1_000_000);
            for _ in 0..n { v.push(x); }
        }
        7 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
        }
        8 => {
            // alternating extremes
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(1_000_000); }
            }
        }
        9 => {
            // increasing
            let base = rng.gen_range_i32(1, 100);
            for i in 0..n {
                let val = (base as i64 + i as i64 * 7) as i32;
                let val = if val > 1_000_000 { 1_000_000 } else if val < 1 { 1 } else { val };
                v.push(val);
            }
        }
        _ => {
            // random small
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
    }
    let _ = t;
    v
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        let out = generate_test_case(&values);
        print_json(&out);
    }
}