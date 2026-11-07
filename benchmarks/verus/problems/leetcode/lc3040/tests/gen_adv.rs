use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 2000,
        values.len() == n,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        2 <= nums.len() <= 2000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            2 <= n <= 2000,
            values.len() == n,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum size
            let n = 2;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
            v
        }
        1 => {
            // maximum size with random values
            let n = 2000;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
            v
        }
        2 => {
            // All same value (every pair sums same)
            let n = rng.gen_range_usize(2, 2000);
            let x = rng.gen_range_i32(1, 1000);
            vec![x; n]
        }
        3 => {
            // Palindrome - first/last pair always sums same
            let n = rng.gen_range_usize(2, 500) * 2;
            let mut v: Vec<i32> = Vec::new();
            for _ in 0..n/2 { v.push(rng.gen_range_i32(1, 1000)); }
            let mut rev: Vec<i32> = v.clone();
            rev.reverse();
            v.extend(rev);
            v
        }
        4 => {
            // Alternating two values
            let n = rng.gen_range_usize(2, 2000);
            let a = rng.gen_range_i32(1, 1000);
            let b = rng.gen_range_i32(1, 1000);
            let mut v = Vec::new();
            for i in 0..n { v.push(if i%2==0 { a } else { b }); }
            v
        }
        5 => {
            // Small values (1..5)
            let n = rng.gen_range_usize(2, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
            v
        }
        6 => {
            // Max values (around 1000)
            let n = rng.gen_range_usize(2, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(995, 1000)); }
            v
        }
        7 => {
            // Target-forced: first+second sum target; design so many pairs match
            let n = rng.gen_range_usize(4, 100);
            let target = rng.gen_range_i32(2, 2000);
            let mut v = Vec::new();
            for _ in 0..n {
                let a = rng.gen_range_i32(1, (target-1).max(1).min(1000));
                let b = target - a;
                if b >= 1 && b <= 1000 {
                    v.push(a);
                    v.push(b);
                } else {
                    v.push(rng.gen_range_i32(1, 1000));
                    v.push(rng.gen_range_i32(1, 1000));
                }
            }
            while v.len() > n { v.pop(); }
            while v.len() < n { v.push(rng.gen_range_i32(1, 1000)); }
            v
        }
        8 => {
            // n=3 small cases
            let n = 3;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
            v
        }
        9 => {
            // Increasing sequence
            let n = rng.gen_range_usize(2, 1000);
            let start = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(((start as i32 + i as i32 - 1) % 1000) + 1);
            }
            v
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(2, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 1000)); }
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode, t);
        let n = values.len();
        if n < 2 || n > 2000 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 1000 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(n, &values);
        print_json(&nums);
    }
}