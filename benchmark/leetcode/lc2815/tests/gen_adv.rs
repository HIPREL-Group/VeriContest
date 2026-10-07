use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10_000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            2 <= n <= 100,
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10_000,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == values[i],
            forall |i: int| 0 <= i < k as int ==> 1 <= #[trigger] nums[i] <= 10_000,
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn max_digit_of(mut n: i32) -> i32 {
    let mut best = 0i32;
    if n == 0 {
        return 0;
    }
    while n > 0 {
        let d = n % 10;
        if d > best {
            best = d;
        }
        n /= 10;
    }
    best
}

fn build(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => 2,
        1 => 100,
        2 => rng.range_usize(2, 5),
        _ => rng.range_usize(2, 100),
    };
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // small minimum case
            v.push(rng.range_i32(1, 9));
            v.push(rng.range_i32(1, 9));
        }
        1 => {
            // max length, all share max digit 9
            for _ in 0..n {
                // ensure at least one 9 digit
                let base = rng.range_i32(1, 999);
                let candidate = base * 10 + 9;
                let c = if candidate > 10_000 { 9 } else { candidate };
                v.push(c);
            }
        }
        2 => {
            // tiny values
            for _ in 0..n {
                v.push(rng.range_i32(1, 20));
            }
        }
        3 => {
            // all same number
            let x = rng.range_i32(1, 10_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        4 => {
            // all powers of 10 (max digit 1)
            let opts = [1, 10, 100, 1000, 10000];
            for _ in 0..n {
                v.push(opts[rng.range_usize(0, 4)]);
            }
        }
        5 => {
            // all distinct max digits
            for i in 0..n {
                let d = ((i % 9) + 1) as i32;
                v.push(d);
            }
        }
        6 => {
            // boundary: 10000
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(10_000);
                } else {
                    v.push(rng.range_i32(1, 10_000));
                }
            }
        }
        7 => {
            // many with digit 9
            for _ in 0..n {
                let opts = [9, 19, 99, 909, 9999, 1009];
                v.push(opts[rng.range_usize(0, 5)]);
            }
        }
        8 => {
            // pairs with same max digit
            for i in 0..n {
                let target_digit = ((i / 2) % 9 + 1) as i32;
                // build number with max digit == target_digit
                let base = rng.range_i32(0, target_digit);
                let num = target_digit * 10 + base;
                v.push(if num == 0 { target_digit } else { num });
            }
        }
        9 => {
            // random general
            for _ in 0..n {
                v.push(rng.range_i32(1, 10_000));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.range_i32(1, 10_000));
            }
        }
    }
    // sanity: clamp
    for i in 0..v.len() {
        if v[i] < 1 {
            v[i] = 1;
        }
        if v[i] > 10_000 {
            v[i] = 10_000;
        }
    }
    let _ = max_digit_of(0); // silence unused warning sometimes
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
    let modes = 10usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}