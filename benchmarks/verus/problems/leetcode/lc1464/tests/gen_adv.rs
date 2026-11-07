use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= vals.len() <= 500,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        2 <= nums.len() <= 500,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == vals.len(),
            2 <= n <= 500,
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == vals[i],
        decreases n - k,
    {
        nums.push(vals[k]);
        k = k + 1;
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_vals(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // min size
            let n = 2usize;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 1000)); }
            v
        }
        1 => {
            // max size
            let n = 500usize;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 1000)); }
            v
        }
        2 => {
            // all ones
            let n = rng.range_usize(2, 500);
            vec![1i32; n]
        }
        3 => {
            // all 1000
            let n = rng.range_usize(2, 500);
            vec![1000i32; n]
        }
        4 => {
            // two large values, rest small
            let n = rng.range_usize(2, 500);
            let mut v = vec![1i32; n];
            let i = rng.range_usize(0, n - 1);
            let mut j = rng.range_usize(0, n - 2);
            if j >= i { j += 1; }
            v[i] = 1000;
            v[j] = 999;
            v
        }
        5 => {
            // max at end
            let n = rng.range_usize(2, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 500)); }
            v[n - 1] = 1000;
            v[n - 2] = 1000;
            v
        }
        6 => {
            // max at start
            let n = rng.range_usize(2, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 500)); }
            v[0] = 1000;
            v[1] = 1000;
            v
        }
        7 => {
            // one unique max
            let n = rng.range_usize(3, 500);
            let mut v = vec![500i32; n];
            let i = rng.range_usize(0, n - 1);
            v[i] = 1000;
            v
        }
        8 => {
            // sorted ascending
            let n = rng.range_usize(2, 500);
            let mut v = Vec::new();
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                if cur < 1000 { cur += 1; }
            }
            v
        }
        9 => {
            // sorted descending
            let n = rng.range_usize(2, 500);
            let mut v = Vec::new();
            let mut cur = 1000i32;
            for _ in 0..n {
                v.push(cur);
                if cur > 1 { cur -= 1; }
            }
            v
        }
        _ => {
            let n = rng.range_usize(2, 500);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 1000)); }
            let _ = t;
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let vals = gen_vals(&mut rng, mode, t);
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}