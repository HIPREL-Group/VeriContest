use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    filler: &Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= filler.len() <= 100,
        1 <= k <= 100,
        forall |i: int| 0 <= i < filler.len() ==> 1 <= #[trigger] filler[i] <= 100,
    ensures
        1 <= res.0.len() <= 100,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100,
        1 <= res.1 <= 100,
{
    let n = filler.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == filler.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < filler.len() ==> 1 <= #[trigger] filler[j] <= 100,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] nums[j] <= 100,
        decreases n - i,
    {
        let v = filler[i];
        nums.push(v);
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

fn build(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // random small
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 10)); }
            let k = rng.gen_range_i32(1, 10);
            (v, k)
        }
        1 => {
            // all equal to k
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_i32(1, 100);
            let v = vec![k; n];
            (v, k)
        }
        2 => {
            // some below k -> impossible
            let n = rng.gen_range_usize(2, 20);
            let k = rng.gen_range_i32(5, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, k)); }
            v[0] = rng.gen_range_i32(1, k - 1);
            (v, k)
        }
        3 => {
            // all >= k with various distinct values
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_i32(1, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(k, 100)); }
            (v, k)
        }
        4 => {
            // max size
            let n = 100;
            let k = rng.gen_range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, k)
        }
        5 => {
            // min size
            let k = rng.gen_range_i32(1, 100);
            let x = rng.gen_range_i32(1, 100);
            (vec![x], k)
        }
        6 => {
            // k = 1
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, 1)
        }
        7 => {
            // k = 100
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            (v, 100)
        }
        8 => {
            // all distinct values >= k, descending chain test
            let k = rng.gen_range_i32(1, 50);
            let mut v = Vec::new();
            let mut x = k;
            while x <= 100 && v.len() < 100 {
                v.push(x);
                x += 1;
            }
            if v.is_empty() { v.push(k); }
            (v, k)
        }
        9 => {
            // two values all >= k
            let k = rng.gen_range_i32(1, 50);
            let a = rng.gen_range_i32(k, 100);
            let b = rng.gen_range_i32(k, 100);
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(a); } else { v.push(b); }
            }
            (v, k)
        }
        _ => {
            // one element below k hidden in middle
            let n = rng.gen_range_usize(3, 100);
            let k = rng.gen_range_i32(2, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(k, 100)); }
            let mid = n / 2;
            v[mid] = rng.gen_range_i32(1, k - 1);
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
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (filler, k) = build(&mut rng, mode);
        // sanity constrain
        let mut f2: Vec<i32> = Vec::new();
        for &x in filler.iter() {
            let mut y = x;
            if y < 1 { y = 1; }
            if y > 100 { y = 100; }
            f2.push(y);
        }
        if f2.is_empty() { f2.push(1); }
        if f2.len() > 100 { f2.truncate(100); }
        let kk = if k < 1 { 1 } else if k > 100 { 100 } else { k };
        let (nums, kout) = generate_test_case(&f2, kk);
        print_json(&nums, kout);
    }
}