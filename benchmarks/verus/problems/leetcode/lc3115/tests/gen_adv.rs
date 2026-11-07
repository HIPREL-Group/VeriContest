use vstd::prelude::*;

verus! {

pub open spec fn is_prime_spec(n: int) -> bool {
    n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
        || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
        || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
        || n == 83 || n == 89 || n == 97
}

pub fn generate_test_case(
    prime_idx: usize,
    prime_val: i32,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        fillers.len() + 1 >= 1,
        fillers.len() + 1 <= 300_000,
        prime_idx < fillers.len() + 1,
        is_prime_spec(prime_val as int),
        1 <= prime_val <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
    ensures
        1 <= nums.len() <= 300_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        exists|i: int| 0 <= i < nums.len() && is_prime_spec(#[trigger] nums[i] as int),
{
    let n: usize = fillers.len() + 1;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 1,
            1 <= n <= 300_000,
            0 <= pos <= n,
            nums.len() == pos,
            prime_idx < n,
            1 <= prime_val <= 100,
            is_prime_spec(prime_val as int),
            0 <= fi <= fillers.len(),
            fi == pos - (if prime_idx < pos { 1usize } else { 0usize }),
            forall|k: int| 0 <= k < pos as int && k == prime_idx as int ==>
                #[trigger] nums[k] == prime_val,
            forall|k: int| 0 <= k < pos as int ==>
                1 <= #[trigger] nums[k] <= 100,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
        decreases n - pos,
    {
        if pos == prime_idx {
            nums.push(prime_val);
        } else {
            assert(fi < fillers.len());
            let v = fillers[fi];
            nums.push(v);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        assert(nums[prime_idx as int] == prime_val);
        assert(is_prime_spec(nums[prime_idx as int] as int));
        assert(exists|i: int| 0 <= i < nums.len() && is_prime_spec(#[trigger] nums[i] as int)) by {
            assert(0 <= prime_idx < nums.len());
            assert(is_prime_spec(nums[prime_idx as int] as int));
        }
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

const PRIMES: [i32; 25] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                           53, 59, 61, 67, 71, 73, 79, 83, 89, 97];

fn is_prime_u8(n: i32) -> bool {
    PRIMES.iter().any(|&p| p == n)
}

fn pick_nonprime(rng: &mut Rng) -> i32 {
    loop {
        let v = rng.gen_range_i32(1, 100);
        if !is_prime_u8(v) {
            return v;
        }
    }
}

fn pick_any(rng: &mut Rng) -> i32 {
    rng.gen_range_i32(1, 100)
}

fn pick_prime(rng: &mut Rng) -> i32 {
    let i = rng.gen_range_usize(0, 24);
    PRIMES[i]
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

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<i32>) {
    // Returns (prime_idx, prime_val, fillers)
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(50, 200),
        4 => 300_000,
        5 => rng.gen_range_usize(1000, 5000),
        6 => rng.gen_range_usize(1, 300_000),
        7 => 100,
        8 => 2 + (t % 50),
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 1000),
    };

    let prime_val = pick_prime(rng);
    let prime_idx: usize = match mode {
        0 => 0,
        1 => 0,
        2 => 0,
        3 => n - 1,
        4 => rng.gen_range_usize(0, n - 1),
        5 => n / 2,
        6 => rng.gen_range_usize(0, n - 1),
        7 => 0,
        8 => rng.gen_range_usize(0, n - 1),
        9 => n - 1,
        _ => rng.gen_range_usize(0, n - 1),
    };

    let filler_count = n - 1;
    let mut fillers: Vec<i32> = Vec::with_capacity(filler_count);
    match mode {
        // all non-primes
        0 | 1 | 3 | 4 | 7 => {
            for _ in 0..filler_count {
                fillers.push(pick_nonprime(rng));
            }
        }
        // all primes
        2 | 5 => {
            for _ in 0..filler_count {
                fillers.push(pick_prime(rng));
            }
        }
        // mixed
        _ => {
            for _ in 0..filler_count {
                fillers.push(pick_any(rng));
            }
        }
    }

    (prime_idx, prime_val, fillers)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (prime_idx, prime_val, fillers) = gen_mode(&mut rng, mode, t);
        let nums = generate_test_case(prime_idx, prime_val, &fillers);
        print_json(&nums);
    }
}