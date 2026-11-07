use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i64>) -> (a: Vec<i64>)
    requires
        1 <= values.len() <= 2000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 2000,
    ensures
        1 <= a.len() <= 2000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 2000,
{
    let n = values.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 2000,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 2000,
            forall|k: int| 0 <= k < a.len() ==> a[k] == values[k],
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 2000,
        decreases n - i,
    {
        a.push(values[i]);
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
    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => {
            // sorted ascending
            for i in 0..n {
                v.push((1 + (i as i64)).min(2000));
            }
        }
        1 => {
            // sorted descending
            for i in 0..n {
                let val = (n as i64 - i as i64).max(1).min(2000);
                v.push(val);
            }
        }
        2 => {
            // all ones
            for _ in 0..n {
                v.push(1);
            }
        }
        3 => {
            // all 2000
            for _ in 0..n {
                v.push(2000);
            }
        }
        4 => {
            // two values
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 2 });
            }
        }
        5 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range(1, 5));
            }
        }
        6 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range(1, 2000));
            }
        }
        7 => {
            // one outlier
            for i in 0..n {
                v.push(if i == 0 { 2000 } else { 1 });
            }
        }
        8 => {
            // one outlier end
            for i in 0..n {
                v.push(if i + 1 == n { 1 } else { 2000 });
            }
        }
        9 => {
            // almost sorted with one swap
            for i in 0..n {
                v.push((1 + (i as i64)).min(2000));
            }
            if n >= 2 {
                let a = rng.gen_usize(0, n - 1);
                let b = rng.gen_usize(0, n - 1);
                v.swap(a, b);
            }
        }
        _ => {
            // random medium
            for _ in 0..n {
                v.push(rng.gen_range(1, 100));
            }
        }
    }
    // safety clamp
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 2000 { *x = 2000; }
    }
    v
}

fn print_json(a: &[i64]) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
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
            0 => 1 + (t % 20),
            1 => 2 + (t % 50),
            2 => 1,
            3 => 2,
            4 => 10 + (t % 30),
            5 => 100 + (t % 50),
            6 => 500 + (t % 100),
            7 => 2000,
            8 => 1000,
            9 => 50 + (t % 50),
            _ => 200 + (t % 300),
        };
        let n = n.max(1).min(2000);
        let values = build_values(&mut rng, mode, n);
        let a = generate_test_case(&values);
        let a_i64: Vec<i64> = a.iter().cloned().collect();
        print_json(&a_i64);
    }
}