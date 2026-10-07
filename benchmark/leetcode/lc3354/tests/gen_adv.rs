use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    zero_idx: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        zero_idx < values.len(),
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= 0,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] <= 100,
        exists|i: int| 0 <= i < nums.len() && nums[i] == 0,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            zero_idx < n,
            0 <= pos <= n,
            nums.len() == pos,
            forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
            forall|k: int| 0 <= k < pos as int && k != zero_idx as int ==>
                #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < pos as int && k == zero_idx as int ==>
                #[trigger] nums[k] == 0,
            forall|k: int| 0 <= k < pos as int ==> 0 <= #[trigger] nums[k] <= 100,
        decreases n - pos,
    {
        if pos == zero_idx {
            nums.push(0);
        } else {
            nums.push(values[pos]);
        }
        pos = pos + 1;
    }

    proof {
        assert(nums[zero_idx as int] == 0);
        assert(exists|i: int| 0 <= i < nums.len() && nums[i] == 0);
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build(rng: &mut Rng, n: usize, values: Vec<i32>) -> Vec<i32> {
    // Ensure at least one zero
    let mut vals = values;
    while vals.len() < n {
        vals.push(0);
    }
    while vals.len() > n {
        vals.pop();
    }
    let zero_idx = rng.gen_range_usize(0, n - 1);
    generate_test_case(zero_idx, &vals)
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 100,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(1, 100),
            6 => rng.gen_range_usize(1, 100),
            7 => 100,
            8 => rng.gen_range_usize(2, 20),
            9 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let mut values: Vec<i32> = Vec::new();
        match mode {
            0 => {
                // single zero
                values.push(0);
            }
            1 => {
                // all zeros
                for _ in 0..n { values.push(0); }
            }
            2 => {
                // max length all zeros
                for _ in 0..n { values.push(0); }
            }
            3 => {
                // small random
                for _ in 0..n { values.push(rng.gen_range_i32(0, 100)); }
            }
            4 => {
                // mostly zeros with a few large
                for _ in 0..n {
                    if rng.next_u64() % 4 == 0 {
                        values.push(rng.gen_range_i32(0, 100));
                    } else {
                        values.push(0);
                    }
                }
            }
            5 => {
                // all max 100 except will force one zero
                for _ in 0..n { values.push(100); }
            }
            6 => {
                // alternating 0 and positive
                for i in 0..n {
                    if i % 2 == 0 { values.push(0); } else { values.push(rng.gen_range_i32(1, 100)); }
                }
            }
            7 => {
                // large with zero at boundary
                for _ in 0..n { values.push(rng.gen_range_i32(0, 100)); }
            }
            8 => {
                // small boundary testing
                for _ in 0..n { values.push(rng.gen_range_i32(0, 3)); }
            }
            9 => {
                // symmetric-ish
                for i in 0..n {
                    let v = if i < n / 2 { rng.gen_range_i32(0, 100) } else { 0 };
                    values.push(v);
                }
            }
            _ => {
                // random general
                for _ in 0..n { values.push(rng.gen_range_i32(0, 100)); }
            }
        }

        let nums = build(&mut rng, n, values);
        print_json(&nums);
    }
}