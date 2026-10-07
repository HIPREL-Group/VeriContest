use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_half: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n_half <= 10000,
        values.len() == 2 * n_half,
        forall|i: int| 0 <= i < values.len() ==> -10000 <= #[trigger] values[i] <= 10000,
    ensures
        2 <= nums.len() <= 20000,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
{
    let total: usize = 2 * n_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < total
        invariant
            total == 2 * n_half,
            1 <= n_half <= 10000,
            values.len() == total,
            0 <= i <= total,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> -10000 <= #[trigger] values[k] <= 10000,
        decreases total - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }

    proof {
        assert(nums.len() == total);
        assert(nums.len() == 2 * n_half);
        assert(nums.len() % 2 == 0) by (nonlinear_arith)
            requires nums.len() == 2 * n_half;
        assert forall|k: int| 0 <= k < nums.len() implies -10000 <= #[trigger] nums[k] <= 10000 by {
            assert(nums[k] == values[k]);
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n_half: usize) -> Vec<i32> {
    let total = 2 * n_half;
    let mut v: Vec<i32> = Vec::with_capacity(total);
    match mode {
        0 => {
            // all zeros
            for _ in 0..total { v.push(0); }
        }
        1 => {
            // all max
            for _ in 0..total { v.push(10000); }
        }
        2 => {
            // all min
            for _ in 0..total { v.push(-10000); }
        }
        3 => {
            // alternating min/max
            for i in 0..total {
                if i % 2 == 0 { v.push(-10000); } else { v.push(10000); }
            }
        }
        4 => {
            // sorted ascending random
            let mut tmp: Vec<i32> = Vec::with_capacity(total);
            for _ in 0..total {
                tmp.push(rng.gen_range_i32(-10000, 10000));
            }
            tmp.sort();
            v = tmp;
        }
        5 => {
            // sorted descending
            let mut tmp: Vec<i32> = Vec::with_capacity(total);
            for _ in 0..total {
                tmp.push(rng.gen_range_i32(-10000, 10000));
            }
            tmp.sort();
            tmp.reverse();
            v = tmp;
        }
        6 => {
            // pairs of equal values
            for _ in 0..n_half {
                let x = rng.gen_range_i32(-10000, 10000);
                v.push(x);
                v.push(x);
            }
        }
        7 => {
            // small range {-1,0,1}
            for _ in 0..total {
                v.push(rng.gen_range_i32(-1, 1));
            }
        }
        8 => {
            // only extremes
            for _ in 0..total {
                if rng.next_u64() % 2 == 0 { v.push(-10000); } else { v.push(10000); }
            }
        }
        9 => {
            // negative values only
            for _ in 0..total {
                v.push(rng.gen_range_i32(-10000, -1));
            }
        }
        _ => {
            // uniform random
            for _ in 0..total {
                v.push(rng.gen_range_i32(-10000, 10000));
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n_half: usize = match mode {
            0 => 1 + (t % 5),
            1 => 10000,
            2 => 5000,
            3 => 1 + (t % 10),
            4 => 100,
            5 => 50,
            6 => 1 + (t % 20),
            7 => 1,
            8 => 2,
            9 => 10 + (t % 30),
            _ => 1 + (rng.gen_range_usize(0, 199)),
        };
        let n_half = if n_half < 1 { 1 } else if n_half > 10000 { 10000 } else { n_half };
        let values = build_values(&mut rng, mode, n_half);
        let nums = generate_test_case(n_half, &values);
        print_json(&nums);
    }
}