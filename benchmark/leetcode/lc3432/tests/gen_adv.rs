use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        2 <= fillers.len() <= 100,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = fillers.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
        decreases n - i,
    {
        nums.push(fillers[i]);
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all even
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50));
            }
        }
        1 => {
            // all odd
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(0, 49) + 1);
            }
        }
        2 => {
            // all 1
            for _ in 0..n { v.push(1); }
        }
        3 => {
            // all 100
            for _ in 0..n { v.push(100); }
        }
        4 => {
            // alternating
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 2 });
            }
        }
        5 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        6 => {
            // one odd, rest even
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50));
            }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 2 * rng.gen_range_i32(0, 49) + 1;
        }
        7 => {
            // odd count of odd numbers (makes sum odd)
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50));
            }
            // flip odd number of indices to odd
            let k = if n >= 3 { 3 } else { 1 };
            for i in 0..k {
                v[i] = 2 * rng.gen_range_i32(0, 49) + 1;
            }
        }
        8 => {
            // even count of odd numbers (sum even)
            for _ in 0..n {
                v.push(2 * rng.gen_range_i32(1, 50));
            }
            if n >= 2 {
                v[0] = 2 * rng.gen_range_i32(0, 49) + 1;
                v[1] = 2 * rng.gen_range_i32(0, 49) + 1;
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 2 + (t % 5),
            1 => 100,
            2 => 2,
            3 => 100,
            4 => 3 + (t % 10),
            5 => 2 + (rng.gen_range_usize(0, 98)),
            6 => 10,
            7 => 50,
            8 => 4 + (t % 20),
            _ => 2 + (t % 99),
        };
        let n = if n < 2 { 2 } else if n > 100 { 100 } else { n };
        let fillers = build_fillers(&mut rng, n, mode);
        let nums = generate_test_case(&fillers);
        print_json(&nums);
    }
}