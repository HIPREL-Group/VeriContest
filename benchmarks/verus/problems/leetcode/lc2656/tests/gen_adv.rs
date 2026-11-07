use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums_in.len() <= 100,
        forall |i: int| 0 <= i < nums_in.len() ==> 1 <= #[trigger] nums_in[i] <= 100,
        1 <= k <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    let mut out: Vec<i32> = Vec::new();
    let n = nums_in.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == nums_in.len(),
            0 <= i <= n,
            out.len() == i,
            forall |j: int| 0 <= j < i ==> 1 <= #[trigger] out[j] <= 100,
            forall |j: int| 0 <= j < i ==> out[j] == nums_in[j],
            forall |j: int| 0 <= j < nums_in.len() ==> 1 <= #[trigger] nums_in[j] <= 100,
        decreases n - i,
    {
        out.push(nums_in[i]);
        i = i + 1;
    }
    (out, k)
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

fn make_nums(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(100); }
        }
        3 => {
            for _ in 0..n { v.push(rng.gen_range_i32(-1, 1).abs().max(1)); }
            // all small
            for i in 0..v.len() { if v[i] < 1 { v[i] = 1; } }
        }
        4 => {
            let x = rng.gen_range_i32(1, 100);
            for _ in 0..n { v.push(x); }
        }
        5 => {
            // mix of negatives-clamped and positives - but must be 1..=100
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100); }
            }
        }
        6 => {
            // increasing
            for i in 0..n {
                let val = ((i % 100) as i32) + 1;
                v.push(val);
            }
        }
        7 => {
            // decreasing
            for i in 0..n {
                let val = 100 - ((i % 100) as i32);
                v.push(val.max(1));
            }
        }
        8 => {
            // one large, rest small
            for _ in 0..n { v.push(1); }
            if n > 0 { v[0] = 100; }
        }
        9 => {
            // one small, rest large
            for _ in 0..n { v.push(100); }
            if n > 0 { v[n-1] = 1; }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
    }
    v
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => 1,
            2 => 100,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(2, 100),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 100),
            9 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let k: i32 = match mode {
            1 => 1,
            2 => 100,
            3 => rng.gen_range_i32(1, 5),
            _ => rng.gen_range_i32(1, 100),
        };

        let nums = make_nums(&mut rng, n, mode);
        // sanity clamp
        let mut nums_clamped: Vec<i32> = nums.iter().map(|&x| {
            if x < 1 { 1 } else if x > 100 { 100 } else { x }
        }).collect();
        if nums_clamped.is_empty() { nums_clamped.push(1); }
        if nums_clamped.len() > 100 { nums_clamped.truncate(100); }

        let (out_nums, out_k) = generate_test_case(&nums_clamped, k);
        print_json(&out_nums, out_k);
    }
}