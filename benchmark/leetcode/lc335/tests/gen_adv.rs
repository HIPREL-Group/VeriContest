use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    let mut result: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            result.len() == i,
            1 <= n <= 100000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100000,
            forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 100000,
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::with_capacity(v.len());
    for x in v.iter() {
        let mut y = *x;
        if y < 1 {
            y = 1;
        }
        if y > 100000 {
            y = 100000;
        }
        out.push(y);
    }
    if out.is_empty() {
        out.push(1);
    }
    if out.len() > 100000 {
        out.truncate(100000);
    }
    out
}

fn gen_random(rng: &mut Rng, n: usize, max_v: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, max_v));
    }
    v
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            gen_random(rng, n, 10)
        }
        1 => {
            // known crossing example 1
            vec![2, 1, 1, 2]
        }
        2 => {
            // known non-crossing
            vec![1, 2, 3, 4]
        }
        3 => {
            // known crossing example 3
            vec![1, 1, 1, 2, 1]
        }
        4 => {
            // strictly increasing spiral (no cross)
            let n = rng.gen_range_usize(4, 20);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i as i32) + 1);
            }
            v
        }
        5 => {
            // strictly decreasing (causes crossings)
            let n = rng.gen_range_usize(4, 20);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((n as i32) - (i as i32));
            }
            v
        }
        6 => {
            // all equal
            let n = rng.gen_range_usize(1, 20);
            let val = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(val);
            }
            v
        }
        7 => {
            // case2 trigger: 5 elements where d[i-1] == d[i-3]
            let a = rng.gen_range_i32(1, 50);
            let b = rng.gen_range_i32(1, 50);
            let c = rng.gen_range_i32(1, 50);
            vec![a, b, c, b, rng.gen_range_i32(1, c)]
        }
        8 => {
            // case3 trigger: 6 elements
            let d4 = rng.gen_range_i32(1, 50);
            let d3 = rng.gen_range_i32(1, 50);
            let d2 = d4 + rng.gen_range_i32(0, 10);
            let d1 = rng.gen_range_i32(1, d3);
            let d5 = rng.gen_range_i32(d3 - d1, 50);
            let d0 = rng.gen_range_i32(d2 - d4, 50);
            vec![d4, d3, d2, d1, d5, d0]
        }
        9 => {
            // large size
            let n = rng.gen_range_usize(100, 1000);
            gen_random(rng, n, 100)
        }
        10 => {
            // max bounds
            vec![100000, 100000, 100000, 100000]
        }
        11 => {
            // single element
            vec![rng.gen_range_i32(1, 100000)]
        }
        12 => {
            // two elements
            vec![rng.gen_range_i32(1, 100000), rng.gen_range_i32(1, 100000)]
        }
        13 => {
            // values near boundary
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(1);
                } else {
                    v.push(100000);
                }
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            gen_random(rng, n, 1000)
        }
    }
}

fn print_json(distance: &[i32]) {
    print!("{{\"distance\":[");
    for i in 0..distance.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", distance[i]);
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
    let modes = 14usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = gen_mode(&mut rng, mode);
        let values = clamp_vec(raw);
        let result = generate_test_case(&values);
        print_json(&result);
    }
}