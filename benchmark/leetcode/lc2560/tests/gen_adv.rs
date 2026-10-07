use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    values: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100000,
        values.len() == n,
        1 <= k_val,
        k_val as int <= (n as int + 1) / 2,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000000,
    ensures
        ({
            let nums = result.0;
            let k = result.1;
            &&& 1 <= nums.len() <= 100000
            &&& nums.len() == n
            &&& (forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000)
            &&& 1 <= k
            &&& k as int <= (nums.len() as int + 1) / 2
            &&& k == k_val
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            nums.len() == i,
            i <= n,
            values.len() == n,
            forall |j: int| 0 <= j < values.len() ==> 1 <= #[trigger] values[j] <= 1000000000,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 1000000000,
            forall |j: int| 0 <= j < i as int ==> nums[j] == values[j],
        decreases n - i,
    {
        nums.push(values[i]);
        i += 1;
    }
    (nums, k_val)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
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

fn build_case(rng: &mut Rng, mode: usize, tc: usize) -> (usize, i32, Vec<i32>) {
    // choose n
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(10, 100),
        4 => rng.gen_range_usize(100, 1000),
        5 => 100000,
        6 => rng.gen_range_usize(1000, 10000),
        7 => 50,
        8 => rng.gen_range_usize(1, 20),
        9 => rng.gen_range_usize(1, 5),
        _ => rng.gen_range_usize(1, 1000),
    };

    // choose values
    let mut values: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            for _ in 0..n {
                values.push(rng.gen_range_i32(1, 100));
            }
        }
        5 => {
            // all same
            let v = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n {
                values.push(v);
            }
        }
        6 => {
            // max values
            for _ in 0..n {
                values.push(1_000_000_000);
            }
        }
        7 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 { values.push(1); } else { values.push(1_000_000_000); }
            }
        }
        8 => {
            // small values
            for _ in 0..n {
                values.push(rng.gen_range_i32(1, 10));
            }
        }
        9 => {
            // increasing
            for i in 0..n {
                let v = ((i as i64 + 1) * 100).min(1_000_000_000) as i32;
                values.push(v);
            }
        }
        _ => {
            let hi = match tc % 3 { 0 => 100, 1 => 1_000_000, _ => 1_000_000_000 };
            for _ in 0..n {
                values.push(rng.gen_range_i32(1, hi));
            }
        }
    }

    // choose k: must be 1 <= k <= (n+1)/2
    let kmax: i32 = ((n as i32) + 1) / 2;
    let k: i32 = if kmax < 1 { 1 } else {
        match mode {
            0 | 1 => 1,
            5 => kmax,
            _ => {
                let choice = rng.gen_range_usize(0, 3);
                match choice {
                    0 => 1,
                    1 => kmax,
                    _ => rng.gen_range_i32(1, kmax),
                }
            }
        }
    };

    (n, k, values)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, k, values) = build_case(&mut rng, mode, t);
        // sanity
        if n == 0 || values.len() != n { continue; }
        let kmax = ((n as i32) + 1) / 2;
        let k_adj = if k < 1 { 1 } else if k > kmax { kmax } else { k };
        let mut bounded: Vec<i32> = Vec::with_capacity(n);
        for v in &values {
            let w = if *v < 1 { 1 } else if *v > 1_000_000_000 { 1_000_000_000 } else { *v };
            bounded.push(w);
        }
        let (nums, kk) = generate_test_case(n, k_adj, &bounded);
        print_json(&nums, kk);
    }
}