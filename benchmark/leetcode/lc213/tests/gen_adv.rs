use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        nums.push(vals[i]);
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

fn build_vals(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
        1 => {
            // length 1
            vec![rng.gen_range_i32(0, 1000)]
        }
        2 => {
            // length 2
            vec![rng.gen_range_i32(0, 1000), rng.gen_range_i32(0, 1000)]
        }
        3 => {
            // length 3 (circle edge case)
            vec![rng.gen_range_i32(0, 1000), rng.gen_range_i32(0, 1000), rng.gen_range_i32(0, 1000)]
        }
        4 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0; n]
        }
        5 => {
            // all same max
            let n = rng.gen_range_usize(1, 100);
            vec![1000; n]
        }
        6 => {
            // max length random
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(0, 1000));
            }
            v
        }
        7 => {
            // alternating high/low
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1000 } else { 0 });
            }
            v
        }
        8 => {
            // strictly increasing-ish
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((i * 10) % 1001) as i32);
            }
            v
        }
        9 => {
            // one big, rest small
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 1000;
            v
        }
        _ => {
            // known examples
            match t % 3 {
                0 => vec![2, 3, 2],
                1 => vec![1, 2, 3, 1],
                _ => vec![1, 2, 3],
            }
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
        let vals = build_vals(&mut rng, mode, t);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}