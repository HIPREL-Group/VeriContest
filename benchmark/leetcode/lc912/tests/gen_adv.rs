use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (res: Vec<i32>)
    requires
        1 <= values.len() <= 50_000,
        forall|i: int| 0 <= i < values.len() ==> -50_000 <= #[trigger] values[i] <= 50_000,
    ensures
        1 <= res.len() <= 50_000,
        forall|i: int| 0 <= i < res.len() ==> -50_000 <= #[trigger] res[i] <= 50_000,
{
    let n = values.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            res.len() == i,
            forall|k: int| 0 <= k < values.len() ==> -50_000 <= #[trigger] values[k] <= 50_000,
            forall|k: int| 0 <= k < i as int ==> res[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> -50_000 <= #[trigger] res[k] <= 50_000,
        decreases n - i,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50_000, 50_000));
            }
            v
        }
        1 => {
            // size 1
            vec![rng.gen_range_i32(-50_000, 50_000)]
        }
        2 => {
            // already sorted ascending
            let n = rng.gen_range_usize(2, 200);
            let mut v: Vec<i32> = Vec::with_capacity(n);
            let mut cur = -50_000i32;
            for _ in 0..n {
                v.push(cur);
                if cur < 50_000 { cur = cur.saturating_add(rng.gen_range_i32(0, 5)); }
            }
            v
        }
        3 => {
            // sorted descending (reverse)
            let n = rng.gen_range_usize(2, 200);
            let mut v: Vec<i32> = Vec::with_capacity(n);
            let mut cur = 50_000i32;
            for _ in 0..n {
                v.push(cur);
                if cur > -50_000 { cur = cur.saturating_sub(rng.gen_range_i32(0, 5)); }
            }
            v
        }
        4 => {
            // all identical
            let n = rng.gen_range_usize(1, 500);
            let val = rng.gen_range_i32(-50_000, 50_000);
            vec![val; n]
        }
        5 => {
            // extremes
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(50_000); } else { v.push(-50_000); }
            }
            v
        }
        6 => {
            // many duplicates with few values
            let n = rng.gen_range_usize(10, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-3, 3));
            }
            v
        }
        7 => {
            // large random
            let n = 50_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50_000, 50_000));
            }
            v
        }
        8 => {
            // nearly sorted with few swaps
            let n = rng.gen_range_usize(10, 1000);
            let mut v: Vec<i32> = (0..n).map(|i| (i as i32) - (n as i32) / 2).collect();
            let swaps = rng.gen_range_usize(1, 5);
            for _ in 0..swaps {
                let a = rng.gen_range_usize(0, n - 1);
                let b = rng.gen_range_usize(0, n - 1);
                v.swap(a, b);
            }
            v
        }
        9 => {
            // zeros and negatives
            let n = rng.gen_range_usize(1, 300);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50_000, 0));
            }
            v
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(100, 2000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-50_000, 50_000));
            }
            let _ = t;
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
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
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        let out = generate_test_case(&values);
        print_json(&out);
    }
}