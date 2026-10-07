use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (gain: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        1 <= gain.len() <= 100,
        forall|i: int| 0 <= i < gain.len() ==> -100 <= #[trigger] gain[i] <= 100,
{
    let n = values.len();
    let mut gain: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            gain.len() == i,
            forall|k: int| 0 <= k < values.len() ==> -100 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> #[trigger] gain[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> -100 <= #[trigger] gain[k] <= 100,
        decreases n - i,
    {
        gain.push(values[i]);
        i = i + 1;
    }
    gain
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
        self.state = self
            .state
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

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        1 => {
            // all max positive
            for _ in 0..n {
                v.push(100);
            }
        }
        2 => {
            // all min negative
            for _ in 0..n {
                v.push(-100);
            }
        }
        3 => {
            // strictly increasing gains -> highest altitude at end
            for i in 0..n {
                let x = -100 + (i as i32 * 3) % 201;
                v.push(x);
            }
        }
        4 => {
            // strictly decreasing gains -> highest at 0
            for i in 0..n {
                let x = 100 - (i as i32 * 3) % 201;
                v.push(x);
            }
        }
        5 => {
            // alternating +100 / -100
            for i in 0..n {
                v.push(if i % 2 == 0 { 100 } else { -100 });
            }
        }
        6 => {
            // negative then positive
            for i in 0..n {
                if i < n / 2 {
                    v.push(-100);
                } else {
                    v.push(100);
                }
            }
        }
        7 => {
            // positive then negative (mimics example 1)
            for i in 0..n {
                if i < n / 2 {
                    v.push(rng.gen_range_i32(-10, 10));
                } else {
                    v.push(rng.gen_range_i32(-100, -1));
                }
            }
        }
        8 => {
            // small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
        }
        9 => {
            // example-like: values that keep peak close to 0
            let opts = [-4i32, -3, -2, -1, 4, 3, 2];
            for i in 0..n {
                v.push(opts[i % opts.len()]);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    // Enforce bounds just in case
    for x in v.iter_mut() {
        if *x < -100 {
            *x = -100;
        }
        if *x > 100 {
            *x = 100;
        }
    }
    v
}

fn print_json(gain: &[i32]) {
    print!("{{\"gain\":[");
    for i in 0..gain.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", gain[i]);
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
            0 => 1,
            1 => 100,
            2 => 100,
            3 => 1 + (t % 100),
            4 => 1 + (t % 100),
            5 => 2 + (t % 99),
            6 => 4 + (t % 50),
            7 => 5,
            8 => rng.gen_range_usize(1, 100),
            9 => 7,
            _ => rng.gen_range_usize(1, 100),
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let values = build_values(&mut rng, mode, n);
        let gain = generate_test_case(&values);
        print_json(&gain);
    }
}