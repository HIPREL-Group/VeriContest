use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i64>,
) -> (a: Vec<i64>)
    requires
        2 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000000000000000i64,
    ensures
        2 <= a.len() <= 100,
        a.len() == values.len(),
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000000000000i64,
{
    let n = values.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000000000000000000i64,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == values[k],
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = ((self.next_u64() as u128) << 64 | self.next_u64() as u128) % span;
        lo + v as i64
    }
}

const MAX_V: i64 = 1_000_000_000_000_000_000;

fn clamp(x: i64) -> i64 {
    if x < 1 { 1 } else if x > MAX_V { MAX_V } else { x }
}

fn build_case(rng: &mut Rng, mode: usize) -> Vec<i64> {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => rng.gen_range_usize(2, 10),
        3 => 100,
        4 => rng.gen_range_usize(2, 100),
        5 => rng.gen_range_usize(2, 100),
        6 => rng.gen_range_usize(2, 100),
        7 => rng.gen_range_usize(2, 100),
        8 => rng.gen_range_usize(2, 100),
        9 => rng.gen_range_usize(2, 100),
        _ => rng.gen_range_usize(2, 100),
    };

    let mut v: Vec<i64> = Vec::with_capacity(n);

    match mode {
        0 | 1 => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 20));
            }
        }
        2 => {
            // alternating even/odd -> d=2 works
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i64(1, 50) * 2);
                } else {
                    let x = rng.gen_range_i64(0, 49) * 2 + 1;
                    v.push(x);
                }
            }
        }
        3 => {
            // large values
            for _ in 0..n {
                v.push(rng.gen_range_i64(MAX_V / 2, MAX_V));
            }
        }
        4 => {
            // all same
            let x = rng.gen_range_i64(1, 1000);
            for _ in 0..n {
                v.push(x);
            }
        }
        5 => {
            // all 1
            for _ in 0..n {
                v.push(1);
            }
        }
        6 => {
            // powers-of-2 alternation
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i64(1, 100) * 6);
                } else {
                    v.push(rng.gen_range_i64(1, 100) * 10);
                }
            }
        }
        7 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, 1_000_000));
            }
        }
        8 => {
            // boundary values
            for i in 0..n {
                if i % 3 == 0 {
                    v.push(1);
                } else if i % 3 == 1 {
                    v.push(MAX_V);
                } else {
                    v.push(rng.gen_range_i64(1, MAX_V));
                }
            }
        }
        9 => {
            // multiples of a prime alternation
            let p: i64 = 100003;
            for i in 0..n {
                if i % 2 == 0 {
                    let k = rng.gen_range_i64(1, 1_000_000);
                    v.push(clamp(k * p));
                } else {
                    let mut x = rng.gen_range_i64(1, 1_000_000_000);
                    if x % p == 0 { x += 1; }
                    v.push(x);
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(1, MAX_V));
            }
        }
    }

    for i in 0..v.len() {
        v[i] = clamp(v[i]);
    }
    v
}

fn print_json(a: &[i64]) {
    // spec asks for x and y fields (per instruction), but problem has array a.
    // The instructions say print JSON per line. Use field "a".
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
        let values = build_case(&mut rng, mode);
        let a = generate_test_case(&values);
        print_json(&a);
    }
}