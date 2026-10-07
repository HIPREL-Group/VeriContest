use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 100);
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
    let n = match mode {
        0 => 1,
        1 => 100,
        2 => 2,
        3 => 3,
        4 => rng.gen_range_usize(1, 100),
        5 => rng.gen_range_usize(1, 10),
        6 => 100,
        7 => 50,
        8 => rng.gen_range_usize(1, 100),
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 100),
    };
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(1, 100),
            1 => 100,
            2 => 1,
            3 => if i % 2 == 0 { 1 } else { 100 },
            4 => if i % 2 == 0 { 100 } else { 1 },
            5 => rng.gen_range_i32(1, 100),
            6 => rng.gen_range_i32(1, 100),
            7 => ((i % 100) as i32) + 1,
            8 => {
                // same value throughout
                let base = ((t % 100) as i32) + 1;
                base
            }
            9 => if i == 0 { 100 } else { 1 },
            _ => rng.gen_range_i32(1, 100),
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