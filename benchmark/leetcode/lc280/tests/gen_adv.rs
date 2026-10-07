use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 50_000,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= nums.len() <= 50_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            0 <= pos <= n,
            1 <= n <= 50_000,
            values.len() == n,
            nums.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 10_000,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < pos as int ==> 0 <= #[trigger] nums[k] <= 10_000,
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all max
            for _ in 0..n { v.push(10_000); }
        }
        2 => {
            // all equal mid
            let x = rng.gen_range_i32(0, 10_000);
            for _ in 0..n { v.push(x); }
        }
        3 => {
            // ascending
            for i in 0..n {
                v.push(((i as i32) % 10_001) as i32);
            }
        }
        4 => {
            // descending
            for i in 0..n {
                let x = 10_000 - ((i as i32) % 10_001);
                v.push(x);
            }
        }
        5 => {
            // alternating already-wiggly
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 10_000 });
            }
        }
        6 => {
            // many duplicates (tricky case for wiggle sort)
            let a = rng.gen_range_i32(0, 10_000);
            let b = rng.gen_range_i32(0, 10_000);
            for i in 0..n {
                v.push(if i % 3 == 0 { a } else { b });
            }
        }
        7 => {
            // nums = [1,1,2,2,3,3,...] - tricky
            for i in 0..n {
                let x = ((i as i32) / 2) % 10_001;
                v.push(x);
            }
        }
        8 => {
            // random small range (lots of dups)
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
        }
        9 => {
            // binary 0/1
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1));
            }
        }
        _ => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10_000));
            }
        }
    }
    v
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
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 3 + (t % 5),
            3 => 50_000,
            4 => 50_000,
            5 => 100,
            6 => 500 + (t % 100),
            7 => 1000,
            8 => 25,
            9 => 7,
            _ => {
                let base = rng.gen_range_usize(1, 2000);
                base
            }
        };

        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(n, &values);
        print_json(&nums);
    }
}