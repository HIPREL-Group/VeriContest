use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (hours: Vec<i32>)
    requires
        1 <= values.len() <= 500000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= hours.len() <= 500000,
        forall |i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut hours: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 500000,
            0 <= pos <= n,
            hours.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] hours[k] == values[k],
            forall |k: int| 0 <= k < pos as int ==> 1 <= #[trigger] hours[k] <= 1_000_000_000,
        decreases n - pos,
    {
        hours.push(values[pos]);
        pos = pos + 1;
    }

    hours
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

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all multiples of 24
            for _ in 0..n {
                let k = rng.gen_range_i32(1, 41_666_666);
                v.push(k * 24);
            }
        }
        1 => {
            // all 24
            for _ in 0..n {
                v.push(24);
            }
        }
        2 => {
            // small random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        3 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
        }
        4 => {
            // pairs summing to multiple of 24
            for i in 0..n {
                if i % 2 == 0 {
                    let a = rng.gen_range_i32(1, 23);
                    v.push(a);
                } else {
                    let prev = v[i-1];
                    let comp = 24 - (prev % 24);
                    v.push(comp);
                }
            }
        }
        5 => {
            // all same value
            let x = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        6 => {
            // large values
            for _ in 0..n {
                v.push(rng.gen_range_i32(999_999_000, 1_000_000_000));
            }
        }
        7 => {
            // values = 12 (pairs of 12+12=24)
            for _ in 0..n {
                v.push(12);
            }
        }
        8 => {
            // alternating 1 and 23
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(23); }
            }
        }
        9 => {
            // multiples of 12 but not 24
            for _ in 0..n {
                let k = rng.gen_range_i32(0, 1000);
                v.push(12 + 24 * k);
            }
        }
        _ => {
            // adversarial mix
            for _ in 0..n {
                let pick = rng.gen_range_usize(0, 2);
                if pick == 0 {
                    v.push(24);
                } else if pick == 1 {
                    v.push(rng.gen_range_i32(1, 1_000_000_000));
                } else {
                    v.push(rng.gen_range_i32(1, 48));
                }
            }
        }
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
            0 => 2 + (t % 10),
            1 => 1,
            2 => 50,
            3 => 1000,
            4 => 100,
            5 => 500,
            6 => 10,
            7 => 200,
            8 => 20,
            9 => 30,
            _ => 5 + (t % 20),
        };

        let values = make_values(&mut rng, mode, n);
        let hours = generate_test_case(&values);
        print_json(&hours);
    }
}