use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k_val: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 30_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
        0 <= k_val <= 1_000_000,
    ensures
        1 <= res.0.len() <= 30_000,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1000,
        0 <= res.1 <= 1_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 30_000,
            pos <= n,
            nums.len() == pos,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
            forall|i: int| 0 <= i < pos as int ==> 1 <= #[trigger] nums[i] <= 1000,
            forall|i: int| 0 <= i < pos as int ==> nums[i] == values[i],
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
    }
    (nums, k_val)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, i32) {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let k: i32;
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
        1 => {
            for _ in 0..n {
                v.push(1);
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
        2 => {
            for _ in 0..n {
                v.push(1000);
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
        3 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            k = 0;
        }
        4 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            k = 1;
        }
        5 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            k = 1_000_000;
        }
        6 => {
            // example 1 pattern
            let base = [10, 5, 2, 6];
            for i in 0..n {
                v.push(base[i % 4]);
            }
            k = 100;
        }
        7 => {
            // alternating small and large
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 1000 });
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
        8 => {
            // mostly 1s with occasional larger
            for _ in 0..n {
                let r = rng.gen_range_i32(0, 10);
                if r < 8 {
                    v.push(1);
                } else {
                    v.push(rng.gen_range_i32(2, 1000));
                }
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
        9 => {
            // small values 1-3
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
            k = rng.gen_range_i32(0, 100);
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            k = rng.gen_range_i32(0, 1_000_000);
        }
    }
    (v, k)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
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
            0 => rng.gen_range_usize(1, 100),
            1 => 30_000,
            2 => rng.gen_range_usize(1, 50),
            3 => rng.gen_range_usize(1, 20),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(1, 500),
            6 => 4 + (t % 20),
            7 => rng.gen_range_usize(2, 200),
            8 => rng.gen_range_usize(1, 1000),
            9 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let (values, k) = make_values(&mut rng, mode, n);
        let (nums, k_out) = generate_test_case(&values, k);
        print_json(&nums, k_out);
    }
}