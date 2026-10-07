use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_half: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n_half <= 500,
        values.len() == n_half,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 500,
    ensures
        nums.len() == 2 * n_half,
        nums.len() % 2 == 0,
        2 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 500,
{
    let n: usize = 2 * n_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == 2 * n_half,
            1 <= n_half <= 500,
            values.len() == n_half,
            0 <= pos <= n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 500,
            forall |k: int| 0 <= k < pos as int ==> 1 <= #[trigger] nums[k] <= 500,
        decreases n - pos,
    {
        let idx: usize = pos / 2;
        assert(idx < n_half);
        let v = values[idx];
        nums.push(v);
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

fn build_values(rng: &mut Rng, mode: usize, n_half: usize) -> Vec<i32> {
    let mut values: Vec<i32> = Vec::with_capacity(n_half);
    match mode {
        0 => {
            // all same value
            let v = rng.gen_range_i32(1, 500);
            for _ in 0..n_half {
                values.push(v);
            }
        }
        1 => {
            // distinct values (up to 500)
            for i in 0..n_half {
                values.push(((i % 500) as i32) + 1);
            }
        }
        2 => {
            // random in [1,500]
            for _ in 0..n_half {
                values.push(rng.gen_range_i32(1, 500));
            }
        }
        3 => {
            // only two distinct values
            let a = rng.gen_range_i32(1, 500);
            let b = rng.gen_range_i32(1, 500);
            for i in 0..n_half {
                if i % 2 == 0 {
                    values.push(a);
                } else {
                    values.push(b);
                }
            }
        }
        4 => {
            // all 1s
            for _ in 0..n_half {
                values.push(1);
            }
        }
        5 => {
            // all 500s (max value)
            for _ in 0..n_half {
                values.push(500);
            }
        }
        6 => {
            // alternating 1 and 500
            for i in 0..n_half {
                if i % 2 == 0 {
                    values.push(1);
                } else {
                    values.push(500);
                }
            }
        }
        7 => {
            // small range [1,5]
            for _ in 0..n_half {
                values.push(rng.gen_range_i32(1, 5));
            }
        }
        8 => {
            // values from upper range [450,500]
            for _ in 0..n_half {
                values.push(rng.gen_range_i32(450, 500));
            }
        }
        9 => {
            // mostly same with one different
            let v = rng.gen_range_i32(1, 500);
            for _ in 0..n_half {
                values.push(v);
            }
            if n_half >= 1 {
                let other = if v == 500 { 1 } else { v + 1 };
                let idx = rng.gen_range_usize(0, n_half - 1);
                values[idx] = other;
            }
        }
        _ => {
            // random
            for _ in 0..n_half {
                values.push(rng.gen_range_i32(1, 500));
            }
        }
    }
    values
}

fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    if n <= 1 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n_half: usize = match mode {
            0 => 1 + (t % 10),
            1 => 500,
            2 => 1 + (t % 500),
            3 => 2 + (t % 50),
            4 => 1 + (t % 20),
            5 => 500 - (t % 100),
            6 => 1 + (t % 100),
            7 => 1 + (t % 250),
            8 => 1 + (t % 80),
            9 => 1 + (t % 30),
            _ => 1 + (t % 500),
        };
        let n_half = if n_half < 1 { 1 } else if n_half > 500 { 500 } else { n_half };

        let mut values = build_values(&mut rng, mode, n_half);
        // guarantee values in [1,500]
        for i in 0..values.len() {
            if values[i] < 1 { values[i] = 1; }
            if values[i] > 500 { values[i] = 500; }
        }

        let nums = generate_test_case(n_half, &values);
        let mut nums_mut = nums;
        shuffle(&mut rng, &mut nums_mut);
        print_json(&nums_mut);
    }
}