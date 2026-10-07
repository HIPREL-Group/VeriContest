use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= n <= 2000,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 2000,
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 2000,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            1 <= n <= 2000,
            out.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 2000,
            forall|k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 2000,
        decreases n - i,
    {
        let v = vals[i];
        assert(1 <= v <= 2000);
        out.push(v);
        i = i + 1;
    }
    out
}

}

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

fn build_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 2000));
            }
        }
        1 => {
            for _ in 0..n {
                v.push(1);
            }
        }
        2 => {
            for _ in 0..n {
                v.push(2000);
            }
        }
        3 => {
            for i in 0..n {
                v.push(((i % 2000) as i32) + 1);
            }
        }
        4 => {
            for i in 0..n {
                let x = (n - i) as i32;
                let xx = if x > 2000 { 2000 } else if x < 1 { 1 } else { x };
                v.push(xx);
            }
        }
        5 => {
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 1 } else { 2000 });
            }
        }
        6 => {
            let base = rng.gen_range_i32(1, 1000);
            for i in 0..n {
                let x = base + (i as i32 % 3);
                let xx = if x > 2000 { 2000 } else { x };
                v.push(xx);
            }
        }
        7 => {
            // powers of 2
            let vals = [1i32, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024];
            for i in 0..n {
                v.push(vals[i % vals.len()]);
            }
        }
        8 => {
            // pairs that sum nicely
            for i in 0..n {
                v.push(((i as i32 * 7) % 2000) + 1);
            }
        }
        9 => {
            // small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 2000));
            }
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"reward_values\":[");
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 2000),
            1 => 2000,
            2 => 2000,
            3 => 1000,
            4 => 1,
            5 => rng.gen_range_usize(1, 100),
            6 => 500,
            7 => 100,
            8 => 2000,
            9 => rng.gen_range_usize(1, 50),
            _ => rng.gen_range_usize(1, 2000),
        };
        let vals = build_vals(&mut rng, mode, n);
        let out = generate_test_case(n, &vals);
        print_json(&out);
    }
}