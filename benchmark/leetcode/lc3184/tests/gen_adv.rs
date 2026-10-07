use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (hours: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= hours.len() <= 100,
        forall|i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
        hours.len() == values.len(),
{
    let mut hours: Vec<i32> = Vec::new();
    let n = values.len();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == values.len(),
            hours.len() == k,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < k as int ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
        decreases n - k,
    {
        let v = values[k];
        assert(1 <= v <= 1_000_000_000);
        hours.push(v);
        k = k + 1;
    }
    hours
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
        let v = (self.next_u64()) % span;
        (lo as i64 + v as i64) as i32
    }
}

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all multiples of 24
            for _ in 0..n {
                let k = rng.gen_range_i32(1, 41666666);
                v.push(k * 24);
            }
        }
        1 => {
            // all value 24
            for _ in 0..n {
                v.push(24);
            }
        }
        2 => {
            // all value 12 (pairs sum to 24)
            for _ in 0..n {
                v.push(12);
            }
        }
        3 => {
            // mix small values 1..48
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 48));
            }
        }
        4 => {
            // values 1..24 (various residues)
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 24));
            }
        }
        5 => {
            // large values near 10^9
            for _ in 0..n {
                v.push(rng.gen_range_i32(999_999_000, 1_000_000_000));
            }
        }
        6 => {
            // value = 1 (no pair forms complete day)
            for _ in 0..n {
                v.push(1);
            }
        }
        7 => {
            // half 6, half 18 -> 6+18=24
            for i in 0..n {
                if i % 2 == 0 { v.push(6); } else { v.push(18); }
            }
        }
        8 => {
            // all 23
            for _ in 0..n {
                v.push(23);
            }
        }
        9 => {
            // values chosen from {24k} and non-multiples
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    let k = rng.gen_range_i32(1, 1000);
                    v.push(k * 24);
                } else {
                    v.push(rng.gen_range_i32(1, 23));
                }
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
    }
    // Ensure all values in [1, 1_000_000_000]
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1_000_000_000 { *x = 1_000_000_000; }
    }
    v
}

fn print_json(hours: &[i32]) {
    print!("{{\"hours\":[");
    for i in 0..hours.len() {
        if i > 0 { print!(","); }
        print!("{}", hours[i]);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 100,
            2 => 50,
            3 => 2 + (t % 30),
            4 => 100,
            5 => 5 + (t % 20),
            6 => 100,
            7 => 2 + (t % 99),
            8 => 1,
            9 => 30 + (t % 60),
            _ => {
                let r = rng.gen_range_usize(1, 100);
                r
            }
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let values = make_values(&mut rng, mode, n);
        let hours = generate_test_case(&values);
        print_json(&hours);
    }
}