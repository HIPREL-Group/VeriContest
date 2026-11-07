use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    values: &Vec<i32>,
) -> (res: Vec<i32>)
    requires
        len % 2 == 0,
        2 <= len <= 10_000,
        values.len() == len,
        forall|i: int| 0 <= i < values.len() ==>
            -100_000 <= #[trigger] values[i] <= 100_000,
    ensures
        res.len() % 2 == 0,
        2 <= res.len() <= 10_000,
        forall|i: int| 0 <= i < res.len() ==>
            -100_000 <= #[trigger] res[i] <= 100_000,
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len == values.len(),
            2 <= len <= 10_000,
            len % 2 == 0,
            0 <= i <= len,
            res.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] res[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==>
                -100_000 <= #[trigger] values[k] <= 100_000,
        decreases len - i,
    {
        res.push(values[i]);
        i = i + 1;
    }
    res
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

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all same
            let x = rng.gen_range_i32(-100_000, 100_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        1 => {
            // all distinct
            let start = rng.gen_range_i32(-100_000, 100_000 - n as i32);
            for i in 0..n {
                v.push(start + i as i32);
            }
        }
        2 => {
            // two types
            let a = rng.gen_range_i32(-100_000, 100_000);
            let mut b = rng.gen_range_i32(-100_000, 100_000);
            if b == a {
                b = if a < 100_000 { a + 1 } else { a - 1 };
            }
            for i in 0..n {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        3 => {
            // exactly n/2 distinct types, each appearing twice
            let half = n / 2;
            let start = rng.gen_range_i32(-100_000, 100_000 - half as i32);
            for i in 0..n {
                v.push(start + (i / 2) as i32);
            }
        }
        4 => {
            // boundary values
            for i in 0..n {
                v.push(if i % 2 == 0 { -100_000 } else { 100_000 });
            }
        }
        5 => {
            // zeros and ones
            for i in 0..n {
                v.push((i % 2) as i32);
            }
        }
        6 => {
            // one unique, rest same
            let x = rng.gen_range_i32(-100_000, 100_000);
            let y = if x < 100_000 { x + 1 } else { x - 1 };
            for i in 0..n {
                v.push(if i == 0 { y } else { x });
            }
        }
        7 => {
            // random small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-3, 3));
            }
        }
        8 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
        }
        9 => {
            // many types but more than n/2
            let types = (n * 3) / 4;
            let clamped = if types == 0 { 1 } else { types };
            for i in 0..n {
                v.push((i % clamped) as i32);
            }
        }
        _ => {
            // random medium range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50, 50));
            }
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"candy_type\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
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
        let n_raw = match mode {
            0 => 2 + (t % 4) * 2,
            1 => 10_000,
            2 => 16 + (t % 8) * 2,
            3 => if t % 2 == 0 { 2 } else { 256 },
            4 => 4 + (t % 6) * 2,
            5 => 64,
            6 => 512,
            7 => 996,
            8 => 10_000,
            9 => 50,
            _ => 500 + (t % 100) * 2,
        };
        // ensure even and in bounds
        let mut n = n_raw;
        if n < 2 { n = 2; }
        if n > 10_000 { n = 10_000; }
        if n % 2 != 0 { n -= 1; }
        if n < 2 { n = 2; }

        let values = build_values(&mut rng, mode, n);
        let res = generate_test_case(n, &values);
        print_json(&res);
    }
}