use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 2000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 2000,
    ensures
        1 <= nums.len() <= 2000,
        forall|j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 2000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 2000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 2000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 2000,
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 1,
        1 => 2000,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(1, 2000),
        4 => 2000,
        5 => 1,
        6 => rng.gen_range_usize(100, 500),
        7 => rng.gen_range_usize(1, 50),
        8 => 2000,
        9 => rng.gen_range_usize(1, 2000),
        _ => rng.gen_range_usize(1, 2000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let x: i32 = match mode {
            0 => rng.gen_range_i32(1, 2000),
            1 => 2000,
            2 => rng.gen_range_i32(1, 9),
            3 => 1,
            4 => rng.gen_range_i32(1, 9),
            5 => rng.gen_range_i32(1, 2000),
            6 => {
                // powers of 10 boundary (10,100,1000)
                let pick = rng.gen_range_usize(0, 3);
                match pick {
                    0 => 10,
                    1 => 100,
                    2 => 1000,
                    _ => rng.gen_range_i32(1, 2000),
                }
            }
            7 => {
                // boundary values
                let pick = rng.gen_range_usize(0, 5);
                match pick {
                    0 => 1,
                    1 => 9,
                    2 => 10,
                    3 => 99,
                    4 => 100,
                    _ => 2000,
                }
            }
            8 => rng.gen_range_i32(1, 2000),
            9 => {
                // digits equal to number (single digits)
                rng.gen_range_i32(1, 9)
            }
            _ => {
                let _ = t;
                rng.gen_range_i32(1, 2000)
            }
        };
        v.push(x);
    }
    v
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
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}