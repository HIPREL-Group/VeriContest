use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= nums.len() <= 10_000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        nums@ == values@,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n: usize = values.len();
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    assert(nums@ =~= values@);
    nums
}

}

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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

// A set of known 4-divisor numbers (products of two distinct primes, or cube of a prime).
const FOUR_DIV: &[i32] = &[
    6, 8, 10, 14, 15, 21, 22, 26, 27, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62,
    65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122, 123, 125,
    129, 133, 134, 141, 142, 143, 145, 146, 155, 158, 159, 161, 166, 177, 178, 183, 185, 187, 194, 201,
    99991, 99989, 99971, // these are primes -> NOT 4-div, skip
];

// Curated 4-div numbers (safe)
const FOUR_DIV_SAFE: &[i32] = &[
    6, 8, 10, 14, 15, 21, 22, 26, 27, 33, 34, 35, 38, 39, 46, 51, 55, 57, 58, 62,
    65, 69, 74, 77, 82, 85, 86, 87, 91, 93, 94, 95, 106, 111, 115, 118, 119, 122, 123, 125,
    129, 133, 134, 141, 142, 143, 145, 146, 155, 158, 159, 161, 166, 177, 178, 183, 185, 187, 194, 201,
];

// Non-4-div numbers
const NOT_FOUR_DIV: &[i32] = &[1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 16, 17, 18, 19, 20, 23, 24, 25, 28, 29, 30, 36, 100, 1000, 10000, 100000];

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all random small
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        1 => {
            // all random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
        2 => {
            // all 1s
            for _ in 0..n {
                v.push(1);
            }
        }
        3 => {
            // all max
            for _ in 0..n {
                v.push(100_000);
            }
        }
        4 => {
            // all known 4-div
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, FOUR_DIV_SAFE.len() - 1);
                v.push(FOUR_DIV_SAFE[idx]);
            }
        }
        5 => {
            // all non-4-div
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, NOT_FOUR_DIV.len() - 1);
                v.push(NOT_FOUR_DIV[idx]);
            }
        }
        6 => {
            // same 4-div repeated (tests duplicates)
            let x = FOUR_DIV_SAFE[rng.gen_range_usize(0, FOUR_DIV_SAFE.len() - 1)];
            for _ in 0..n {
                v.push(x);
            }
        }
        7 => {
            // primes (which have exactly 2 divisors)
            let primes: [i32; 20] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71];
            for _ in 0..n {
                v.push(primes[rng.gen_range_usize(0, primes.len() - 1)]);
            }
        }
        8 => {
            // perfect squares (often 3 divisors if p^2)
            let squares: [i32; 10] = [4, 9, 25, 49, 121, 169, 289, 361, 529, 841];
            for _ in 0..n {
                v.push(squares[rng.gen_range_usize(0, squares.len() - 1)]);
            }
        }
        9 => {
            // mix: half 4-div, half not
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(FOUR_DIV_SAFE[rng.gen_range_usize(0, FOUR_DIV_SAFE.len() - 1)]);
                } else {
                    v.push(NOT_FOUR_DIV[rng.gen_range_usize(0, NOT_FOUR_DIV.len() - 1)]);
                }
            }
        }
        _ => {
            // small random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    // Clamp all to [1, 100000]
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100_000 { *x = 100_000; }
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 20),
            1 => rng.gen_range_usize(1, 100),
            2 => rng.gen_range_usize(1, 50),
            3 => rng.gen_range_usize(1, 50),
            4 => rng.gen_range_usize(1, 50),
            5 => rng.gen_range_usize(1, 50),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 50),
            8 => rng.gen_range_usize(1, 30),
            _ => rng.gen_range_usize(1, 200),
        };
        let n = if n < 1 { 1 } else if n > 10_000 { 10_000 } else { n };
        let values = make_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }

    // A few edge cases
    let edge1 = vec![1i32];
    let r1 = generate_test_case(&edge1);
    print_json(&r1);

    let edge2 = vec![100_000i32];
    let r2 = generate_test_case(&edge2);
    print_json(&r2);

    let edge3 = vec![21i32, 4, 7];
    let r3 = generate_test_case(&edge3);
    print_json(&r3);

    let edge4 = vec![21i32, 21];
    let r4 = generate_test_case(&edge4);
    print_json(&r4);
}