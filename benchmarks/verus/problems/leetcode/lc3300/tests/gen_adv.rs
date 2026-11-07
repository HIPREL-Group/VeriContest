use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = values.len();
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 10000,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 10000);
        nums.push(v);
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

    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn build(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 1,
        1 => 100,
        2 => (rng.gen_range(1, 10) as usize),
        3 => (rng.gen_range(1, 100) as usize),
        _ => (rng.gen_range(1, 100) as usize),
    };
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let x: i32 = match mode {
            0 => 1,
            1 => 10000,
            2 => rng.gen_range(1, 9) as i32, // small single-digit
            3 => {
                // powers-like: 10, 100, 1000, 10000
                let k = rng.gen_range(0, 4);
                match k {
                    0 => 10,
                    1 => 100,
                    2 => 1000,
                    _ => 10000,
                }
            }
            4 => 9999, // max digit sum candidates
            5 => {
                // numbers with high digit sums
                let opts = [999, 998, 989, 899, 9999, 9998, 9989];
                opts[(rng.next_u64() as usize) % opts.len()]
            }
            6 => {
                // numbers with low digit sums
                let opts = [1, 10, 100, 1000, 10000, 20, 200];
                opts[(rng.next_u64() as usize) % opts.len()]
            }
            7 => {
                // boundary: multiples of 10
                (rng.gen_range(1, 1000) * 10) as i32
            }
            8 => rng.gen_range(1, 10000) as i32,
            9 => {
                // mix of small and large
                if rng.next_u64() % 2 == 0 { rng.gen_range(1, 9) as i32 } else { rng.gen_range(9990, 10000) as i32 }
            }
            _ => rng.gen_range(1, 10000) as i32,
        };
        let x = if x < 1 { 1 } else if x > 10000 { 10000 } else { x };
        v.push(x);
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}