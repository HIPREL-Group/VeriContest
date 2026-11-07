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
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            1 <= values.len() <= 100,
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

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::with_capacity(v.len());
    for x in v {
        let y = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        out.push(y);
    }
    out
}

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // all equal
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(1, 100);
            vec![v; n]
        }
        1 => {
            // strictly ascending all the way
            let n = rng.gen_range_usize(1, 100);
            let start = rng.gen_range_i32(1, 100i32.saturating_sub(n as i32).max(1));
            let start = if start + (n as i32) - 1 > 100 { 1 } else { start };
            let mut v = Vec::new();
            for i in 0..n {
                v.push(start + i as i32);
            }
            clamp_vec(v)
        }
        2 => {
            // strictly descending
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let start = 100i32.min(n as i32);
            for i in 0..n {
                let x = start - i as i32;
                v.push(if x < 1 { 1 } else { x });
            }
            clamp_vec(v)
        }
        3 => {
            // single element
            vec![rng.gen_range_i32(1, 100)]
        }
        4 => {
            // alternating pattern
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100); }
            }
            v
        }
        5 => {
            // ascending then reset pattern
            let n = rng.gen_range_usize(5, 100);
            let mut v = Vec::new();
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur += 1;
                if cur > 50 { cur = 1; }
            }
            v
        }
        6 => {
            // maximum length all 100
            vec![100; 100]
        }
        7 => {
            // length 100 all 1
            vec![1; 100]
        }
        8 => {
            // two equal then ascending
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::new();
            v.push(50);
            v.push(50);
            let mut cur = 51i32;
            for _ in 2..n {
                v.push(cur);
                if cur < 100 { cur += 1; } else { cur = 1; }
            }
            v
        }
        9 => {
            // random
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        _ => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
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
        let values = build_mode(&mut rng, mode);
        let values = clamp_vec(values);
        let values = if values.is_empty() { vec![1] } else if values.len() > 100 { values[..100].to_vec() } else { values };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}