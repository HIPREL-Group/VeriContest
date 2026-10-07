use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            1 <= n <= 100_000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        1 => {
            // contains 1 -> good
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            let one_pos = rng.gen_range_usize(0, n - 1);
            for i in 0..n {
                if i == one_pos {
                    v.push(1);
                } else {
                    v.push(rng.gen_range_i32(1, 1_000_000_000));
                }
            }
            v
        }
        2 => {
            // all same even -> not good
            let n = rng.gen_range_usize(2, 20);
            let x = rng.gen_range_i32(1, 500_000_000) * 2;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(x);
            }
            v
        }
        3 => {
            // coprime pair
            let mut v = Vec::new();
            v.push(3);
            v.push(5);
            let extra = rng.gen_range_usize(0, 10);
            for _ in 0..extra {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            v
        }
        4 => {
            // all multiples of some prime
            let primes = [2i32, 3, 5, 7, 11, 13];
            let p = primes[rng.gen_range_usize(0, 5)];
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::new();
            for _ in 0..n {
                let m = rng.gen_range_i32(1, 1_000_000_000 / p);
                v.push(m * p);
            }
            v
        }
        5 => {
            // singleton 1
            let mut v = Vec::new();
            v.push(1);
            v
        }
        6 => {
            // singleton not 1
            let mut v = Vec::new();
            v.push(rng.gen_range_i32(2, 1_000_000_000));
            v
        }
        7 => {
            // large values near 10^9
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(999_999_000, 1_000_000_000));
            }
            v
        }
        8 => {
            // big n
            let n = 100_000usize;
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((i as i32) % 1_000_000_000) + 1);
            }
            v
        }
        9 => {
            // two equal primes
            let primes = [2i32, 3, 5, 7, 11, 13, 17, 19, 23];
            let p = primes[rng.gen_range_usize(0, 8)];
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(p);
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        // sanity filter
        let mut ok = values.len() >= 1 && values.len() <= 100_000;
        if ok {
            for &x in &values {
                if x < 1 || x > 1_000_000_000 {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}