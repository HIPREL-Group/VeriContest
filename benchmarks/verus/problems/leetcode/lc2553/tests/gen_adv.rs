use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= vals.len() <= 1000,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100000,
    ensures
        1 <= result.len() <= 1000,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    let n = vals.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            result.len() == i,
            1 <= n <= 1000,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] result[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> result[k] == vals[k],
        decreases n - i,
    {
        result.push(vals[i]);
        i = i + 1;
    }
    result
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

fn build_vec(values: Vec<i32>) -> Vec<i32> {
    values
}

fn make_test(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Single element minimum
            vec![1]
        }
        1 => {
            // Single element max
            vec![100000]
        }
        2 => {
            // Small random array
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
            v
        }
        3 => {
            // Max length 1000, all 1
            let mut v = Vec::new();
            for _ in 0..1000 {
                v.push(1);
            }
            v
        }
        4 => {
            // Max length, all max
            let mut v = Vec::new();
            for _ in 0..1000 {
                v.push(100000);
            }
            v
        }
        5 => {
            // All single digit
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 9));
            }
            v
        }
        6 => {
            // Numbers with trailing zeros
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            let candidates = [10, 100, 1000, 10000, 100000, 1010, 10010, 90900];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, candidates.len() - 1);
                v.push(candidates[idx]);
            }
            v
        }
        7 => {
            // Repeated digits
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            let candidates = [11, 22, 333, 4444, 55555, 99999, 11111];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, candidates.len() - 1);
                v.push(candidates[idx]);
            }
            v
        }
        8 => {
            // Boundary digit counts
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let candidates = [9, 10, 99, 100, 999, 1000, 9999, 10000, 99999, 100000];
            for _ in 0..n {
                let idx = rng.gen_range_usize(0, candidates.len() - 1);
                v.push(candidates[idx]);
            }
            v
        }
        9 => {
            // Example 1
            vec![13, 25, 83, 77]
        }
        _ => {
            // Random with various sizes
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100000));
            }
            let _ = t;
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let vals = make_test(&mut rng, mode, t);
        // Safety: clamp to constraints
        let mut safe: Vec<i32> = Vec::new();
        for &x in &vals {
            let v = if x < 1 { 1 } else if x > 100000 { 100000 } else { x };
            safe.push(v);
        }
        if safe.is_empty() {
            safe.push(1);
        }
        if safe.len() > 1000 {
            safe.truncate(1000);
        }
        let input = build_vec(safe);
        let result = generate_test_case(&input);
        print_json(&result);
    }
}