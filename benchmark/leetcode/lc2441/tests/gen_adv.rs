use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> -1000 <= #[trigger] values[i] <= 1000,
        forall |i: int| 0 <= i < values.len() ==> values[i] != 0,
    ensures
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> nums[i] != 0,
        nums.len() == values.len(),
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == values[i],
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut pos: usize = 0;
    while pos < n
        invariant
            0 <= pos <= n,
            n == values.len(),
            nums.len() == pos,
            forall |i: int| 0 <= i < pos as int ==> #[trigger] nums[i] == values[i],
        decreases n - pos,
    {
        nums.push(values[pos]);
        pos = pos + 1;
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

    fn gen_nonzero_i32(&mut self, lo: i32, hi: i32) -> i32 {
        loop {
            let span = (hi - lo + 1) as u64;
            let v = lo + ((self.next_u64() % span) as i32);
            if v != 0 {
                return v;
            }
        }
    }
}

fn build_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_nonzero_i32(lo, hi));
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

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random, all positive (no match)
            let n = rng.gen_range_usize(1, 10);
            build_random(rng, n, 1, 1000)
        }
        1 => {
            // small random, all negative
            let n = rng.gen_range_usize(1, 10);
            build_random(rng, n, -1000, -1)
        }
        2 => {
            // full range random
            let n = rng.gen_range_usize(1, 50);
            build_random(rng, n, -1000, 1000)
        }
        3 => {
            // guaranteed pair k and -k
            let n = rng.gen_range_usize(2, 50);
            let mut v = build_random(rng, n, -1000, 1000);
            let k = rng.gen_range_usize(1, 1000) as i32;
            let i = rng.gen_range_usize(0, n - 1);
            let mut j = rng.gen_range_usize(0, n - 2);
            if j >= i { j += 1; }
            v[i] = k;
            v[j] = -k;
            v
        }
        4 => {
            // max k = 1000 present with -1000
            let n = rng.gen_range_usize(2, 100);
            let mut v = build_random(rng, n, -999, 999);
            for x in v.iter_mut() {
                if *x == 0 { *x = 1; }
            }
            v[0] = 1000;
            v[1] = -1000;
            v
        }
        5 => {
            // k = 1 only
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = Vec::with_capacity(n);
            for i in 0..n {
                if i == 0 { v.push(1); }
                else if i == 1 { v.push(-1); }
                else {
                    let mut x = rng.gen_nonzero_i32(2, 1000);
                    if x == 1 || x == -1 { x = 2; }
                    v.push(x);
                }
            }
            v
        }
        6 => {
            // length 1
            vec![rng.gen_nonzero_i32(-1000, 1000)]
        }
        7 => {
            // length 1000, heavy
            let n = 1000;
            build_random(rng, n, -1000, 1000)
        }
        8 => {
            // many duplicates
            let n = rng.gen_range_usize(2, 200);
            let k = rng.gen_range_usize(1, 1000) as i32;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 { v.push(k); } else { v.push(-k); }
            }
            v
        }
        9 => {
            // multiple pairs, need max
            let n = rng.gen_range_usize(4, 200);
            let mut v = build_random(rng, n, -1000, 1000);
            let idx = rng.gen_range_usize(0, n - 4);
            v[idx] = 5;
            v[idx+1] = -5;
            v[idx+2] = 100;
            v[idx+3] = -100;
            v
        }
        _ => {
            // only positives with negatives not matching
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_nonzero_i32(1, 500));
                } else {
                    v.push(rng.gen_nonzero_i32(-1000, -501));
                }
            }
            v
        }
    }
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
        let values = make_case(&mut rng, mode);
        // Enforce constraints defensively (though make_case already does it)
        let mut clean: Vec<i32> = Vec::with_capacity(values.len());
        for &x in &values {
            let y = if x == 0 { 1 } else if x > 1000 { 1000 } else if x < -1000 { -1000 } else { x };
            clean.push(y);
        }
        if clean.is_empty() { clean.push(1); }
        if clean.len() > 1000 { clean.truncate(1000); }
        let nums = generate_test_case(&clean);
        print_json(&nums);
    }
}