use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> -100 <= #[trigger] values[k] <= 100,
        decreases n - i,
    {
        nums.push(values[i]);
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

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // All positive
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        1 => {
            // All negative
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, -1));
            }
        }
        2 => {
            // All zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        3 => {
            // All -100 (worst case)
            for _ in 0..n {
                v.push(-100);
            }
        }
        4 => {
            // All 100
            for _ in 0..n {
                v.push(100);
            }
        }
        5 => {
            // Mixed random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
        6 => {
            // Large negative front, positive after
            let half = n / 2;
            for _ in 0..half {
                v.push(rng.gen_range_i32(-100, -50));
            }
            for _ in half..n {
                v.push(rng.gen_range_i32(50, 100));
            }
        }
        7 => {
            // Positive front, negative after
            let half = n / 2;
            for _ in 0..half {
                v.push(rng.gen_range_i32(50, 100));
            }
            for _ in half..n {
                v.push(rng.gen_range_i32(-100, -50));
            }
        }
        8 => {
            // Alternating
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(-100, -1));
                } else {
                    v.push(rng.gen_range_i32(1, 100));
                }
            }
        }
        9 => {
            // Single big drop at some index
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
            }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = -100;
            }
        }
        _ => {
            // Small values near zero
            for _ in 0..n {
                v.push(rng.gen_range_i32(-3, 3));
            }
        }
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
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 100,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(1, 100),
            5 => 50,
            _ => rng.gen_range_usize(1, 100),
        };

        let values = make_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}