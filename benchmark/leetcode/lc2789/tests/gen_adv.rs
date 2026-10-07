use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000000,
    ensures
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000000,
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // tiny arrays, length 1
            vec![rng.gen_range_i32(1, 1_000_000)]
        }
        1 => {
            // small random arrays
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
            v
        }
        2 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur: i32 = 1;
            for _ in 0..n {
                v.push(cur);
                if cur < 1_000_000 { cur += 1; }
            }
            v
        }
        3 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur: i32 = 1_000_000;
            for _ in 0..n {
                v.push(cur);
                if cur > 1 { cur -= 1; }
            }
            v
        }
        4 => {
            // all ones
            let n = rng.gen_range_usize(1, 1000);
            vec![1i32; n]
        }
        5 => {
            // all max
            let n = rng.gen_range_usize(1, 1000);
            vec![1_000_000i32; n]
        }
        6 => {
            // large size
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
            v
        }
        7 => {
            // large size increasing (can fully merge)
            let n = 100_000usize;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = ((i % 1_000_000) as i32) + 1;
                v.push(x);
            }
            v
        }
        8 => {
            // large size decreasing (cannot merge)
            let n = rng.gen_range_usize(100, 1000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = (n - i) as i32;
                v.push(if x < 1 { 1 } else if x > 1_000_000 { 1_000_000 } else { x });
            }
            v
        }
        9 => {
            // alternating
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(1_000_000); }
            }
            v
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(100, 5000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1_000_000)); }
            v
        }
    }
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_values(&mut rng, mode, t);
        if values.is_empty() || values.len() > 100_000 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 1_000_000 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}