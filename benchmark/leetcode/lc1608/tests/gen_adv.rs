use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = vals.len();
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        nums.push(vals[i]);
        i += 1;
    }
    nums
}

}

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

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // All zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        1 => {
            // Single element
            let v = rng.gen_range_i32(0, 1000);
            vec![v]
        }
        2 => {
            // All same value
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(0, 1000);
            vec![v; n]
        }
        3 => {
            // [0..n-1] pattern
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(i as i32);
            }
            v
        }
        4 => {
            // x equals n case: all elements >= n
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(n as i32, 1000));
            }
            v
        }
        5 => {
            // boundary x: half big, half small
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            let half = n / 2;
            for _ in 0..half {
                v.push(rng.gen_range_i32(500, 1000));
            }
            for _ in half..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            v
        }
        6 => {
            // All 1000
            let n = rng.gen_range_usize(1, 100);
            vec![1000i32; n]
        }
        7 => {
            // tricky: values equal to count
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_usize(0, n);
            let mut v = Vec::new();
            for _ in 0..x {
                v.push(rng.gen_range_i32(x as i32, 1000));
            }
            for _ in x..n {
                v.push(rng.gen_range_i32(0, if x == 0 { 0 } else { x as i32 - 1 }));
            }
            v
        }
        8 => {
            // large n random
            let n = 100;
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
        9 => {
            // small n random
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
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
    let total = 220usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let vals = build_mode(&mut rng, mode);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}