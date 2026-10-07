use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
    ensures
        2 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
{
    let n: usize = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            2 <= n <= 100_000,
            0 <= pos <= n,
            nums.len() == pos,
            forall|k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
    }

    nums
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v
        }
        1 => {
            // all zeros
            let n = rng.gen_range_usize(2, 50);
            vec![0i32; n]
        }
        2 => {
            // all positive max
            let n = rng.gen_range_usize(2, 50);
            vec![100_000i32; n]
        }
        3 => {
            // all negative min
            let n = rng.gen_range_usize(2, 50);
            vec![-100_000i32; n]
        }
        4 => {
            // alternating positive/negative extremes
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 100_000 } else { -100_000 });
            }
            v
        }
        5 => {
            // large size
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            v
        }
        6 => {
            // n=2 edge
            let a = rng.gen_range_i32(-100_000, 100_000);
            let b = rng.gen_range_i32(-100_000, 100_000);
            vec![a, b]
        }
        7 => {
            // big first, tiny rest: all splits valid
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            v.push(100_000);
            for _ in 1..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v
        }
        8 => {
            // tiny first, big rest: few splits valid
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..(n-1) {
                v.push(rng.gen_range_i32(-100, 100));
            }
            v.push(100_000);
            v
        }
        9 => {
            // boundary: sum exactly zero after split
            let n = rng.gen_range_usize(4, 20);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { -1 });
            }
            v
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(100, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100_000, 100_000));
            }
            // vary based on t
            if t % 3 == 0 {
                for x in v.iter_mut() { *x = x.abs(); }
            }
            v
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
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
        let values = build_mode(&mut rng, mode, t);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}