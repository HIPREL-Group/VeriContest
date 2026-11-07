use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    filler: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= filler.len() <= 1000,
        forall |i: int| 0 <= i < filler.len() ==> 1 <= #[trigger] filler[i] <= 1000,
    ensures
        2 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let n = filler.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == filler.len(),
            2 <= n <= 1000,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < filler.len() ==> 1 <= #[trigger] filler[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == filler[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        nums.push(filler[i]);
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

fn build_nums(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        1 => {
            // all ones
            let n = rng.gen_range_usize(2, 100);
            vec![1i32; n]
        }
        2 => {
            // all same value
            let x = rng.gen_range_i32(1, 1000);
            let n = rng.gen_range_usize(2, 100);
            vec![x; n]
        }
        3 => {
            // min=1, max=something; GCD=1
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            v.push(1);
            for _ in 1..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        4 => {
            // large size boundary
            let n = 1000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
            v
        }
        5 => {
            // size 2
            vec![rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)]
        }
        6 => {
            // min=max=1000
            let n = rng.gen_range_usize(2, 20);
            vec![1000i32; n]
        }
        7 => {
            // coprime smallest/largest
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::with_capacity(n);
            v.push(7);
            v.push(13);
            for _ in 2..n {
                v.push(rng.gen_range_i32(8, 12));
            }
            v
        }
        8 => {
            // powers of 2
            let n = rng.gen_range_usize(2, 20);
            let pows = [2, 4, 8, 16, 32, 64, 128, 256, 512];
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, pows.len() - 1);
                v.push(pows[idx]);
            }
            v
        }
        9 => {
            // multiples of a prime
            let primes = [3, 5, 7, 11, 13];
            let p = primes[t % primes.len()];
            let n = rng.gen_range_usize(2, 30);
            let mut v = Vec::with_capacity(n);
            let max_mult = 1000 / p;
            for _ in 0..n {
                let m = rng.gen_range_i32(1, max_mult);
                v.push(m * p);
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let filler = build_nums(mode, &mut rng, t);
        // ensure 2<=len<=1000 and 1<=each<=1000
        if filler.len() < 2 || filler.len() > 1000 { continue; }
        let mut ok = true;
        for &x in &filler {
            if x < 1 || x > 1000 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(&filler);
        print_json(&nums);
    }
}