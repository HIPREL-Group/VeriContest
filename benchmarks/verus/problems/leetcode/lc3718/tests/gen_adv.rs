use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    k: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= k <= 100,
        1 <= fillers.len() <= 100,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = fillers.len();
    while i < n
        invariant
            n == fillers.len(),
            i <= n,
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100,
            forall |j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 100,
        decreases n - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, k)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_adversarial(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // k=1, nums contains 1..n but missing some small multiple
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for i in 0..n { v.push((i as i32) + 2); } // missing 1
            (v, 1)
        }
        1 => {
            // k=2, all multiples of 2 up to some point
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for i in 0..n { v.push(((i as i32) + 1) * 2); }
            if v.iter().any(|&x| x > 100) {
                let mut vv = Vec::new();
                for i in 0..n { vv.push(2); }
                (vv, 2)
            } else {
                (v, 2)
            }
        }
        2 => {
            // k=100, nums has 100
            let v = vec![100i32];
            (v, 100)
        }
        3 => {
            // k=100, nums without 100
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 99)); }
            (v, 100)
        }
        4 => {
            // single element
            let k = rng.gen_range_i32(1, 100);
            let x = rng.gen_range_i32(1, 100);
            (vec![x], k)
        }
        5 => {
            // duplicates
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(x); }
            let k = rng.gen_range_i32(1, 100);
            (v, k)
        }
        6 => {
            // nums filled with 1s, k varies
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(1); }
            let k = rng.gen_range_i32(1, 100);
            (v, k)
        }
        7 => {
            // max size random
            let mut v = Vec::new();
            for _ in 0..100 { v.push(rng.gen_range_i32(1, 100)); }
            let k = rng.gen_range_i32(1, 100);
            (v, k)
        }
        8 => {
            // k such that 2k > 100, so only k can exist
            let k = rng.gen_range_i32(51, 100);
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(k); }
            (v, k)
        }
        9 => {
            // all 100s
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(100); }
            let k = rng.gen_range_i32(1, 100);
            (v, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            let k = rng.gen_range_i32(1, 100);
            (v, k)
        }
    }
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (fillers, k) = build_adversarial(&mut rng, mode);
        // Ensure fillers satisfy requires: 1 <= len <= 100 and 1 <= v <= 100
        let mut f2: Vec<i32> = Vec::new();
        for &v in &fillers {
            if v >= 1 && v <= 100 && f2.len() < 100 {
                f2.push(v);
            }
        }
        if f2.is_empty() {
            f2.push(1);
        }
        let kk = if k >= 1 && k <= 100 { k } else { 1 };
        let (nums, kout) = generate_test_case(kk, &f2);
        print_json(&nums, kout);
    }
}