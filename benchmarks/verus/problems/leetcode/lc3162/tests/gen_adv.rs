use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    k: i32,
) -> (res: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= nums1.len() <= 50,
        1 <= nums2.len() <= 50,
        forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 50,
        forall|j: int| 0 <= j < nums2.len() ==> 1 <= #[trigger] nums2[j] <= 50,
        1 <= k <= 50,
    ensures
        1 <= res.0.len() <= 50,
        1 <= res.1.len() <= 50,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 50,
        forall|j: int| 0 <= j < res.1.len() ==> 1 <= #[trigger] res.1[j] <= 50,
        1 <= res.2 <= 50,
{
    (nums1, nums2, k)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build(nums1: Vec<i32>, nums2: Vec<i32>, k: i32) -> (Vec<i32>, Vec<i32>, i32) {
    // Clamp each element to valid range.
    let mut v1: Vec<i32> = nums1.into_iter().map(|x| {
        let y = if x < 1 { 1 } else if x > 50 { 50 } else { x };
        y
    }).collect();
    if v1.is_empty() { v1.push(1); }
    if v1.len() > 50 { v1.truncate(50); }

    let mut v2: Vec<i32> = nums2.into_iter().map(|x| {
        let y = if x < 1 { 1 } else if x > 50 { 50 } else { x };
        y
    }).collect();
    if v2.is_empty() { v2.push(1); }
    if v2.len() > 50 { v2.truncate(50); }

    let kk = if k < 1 { 1 } else if k > 50 { 50 } else { k };

    generate_test_case(v1, v2, kk)
}

fn print_json(nums1: &[i32], nums2: &[i32], k: i32) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn gen_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, i32) {
    match mode {
        0 => {
            // minimal sizes
            let n = 1;
            let m = 1;
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 50)).collect();
            let k = rng.gen_range_i32(1, 50);
            build(nums1, nums2, k)
        }
        1 => {
            // max sizes
            let n = 50;
            let m = 50;
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 50)).collect();
            let k = rng.gen_range_i32(1, 50);
            build(nums1, nums2, k)
        }
        2 => {
            // k = 1 (all pairs where nums1[i] % nums2[j] == 0)
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 50)).collect();
            build(nums1, nums2, 1)
        }
        3 => {
            // k = 50 (hard to divide)
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 50)).collect();
            build(nums1, nums2, 50)
        }
        4 => {
            // All 1s
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = vec![1; n];
            let nums2: Vec<i32> = vec![1; m];
            let k = rng.gen_range_i32(1, 50);
            build(nums1, nums2, k)
        }
        5 => {
            // All 50s
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = vec![50; n];
            let nums2: Vec<i32> = vec![50; m];
            let k = rng.gen_range_i32(1, 50);
            build(nums1, nums2, k)
        }
        6 => {
            // nums1 large, nums2 small -> many divisions possible
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(40, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 5)).collect();
            let k = rng.gen_range_i32(1, 10);
            build(nums1, nums2, k)
        }
        7 => {
            // nums1 small, nums2 large -> few divisions
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 5)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(40, 50)).collect();
            let k = rng.gen_range_i32(1, 10);
            build(nums1, nums2, k)
        }
        8 => {
            // Powers of 2
            let pow2: Vec<i32> = vec![1, 2, 4, 8, 16, 32];
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| pow2[rng.gen_range_usize(0, pow2.len() - 1)]).collect();
            let nums2: Vec<i32> = (0..m).map(|_| pow2[rng.gen_range_usize(0, pow2.len() - 1)]).collect();
            let k = rng.gen_range_i32(1, 8);
            build(nums1, nums2, k)
        }
        9 => {
            // Example 1
            build(vec![1, 3, 4], vec![1, 3, 4], 1)
        }
        10 => {
            // Example 2
            build(vec![1, 2, 4, 12], vec![2, 4], 3)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 50);
            let nums1: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            let nums2: Vec<i32> = (0..m).map(|_| rng.gen_range_i32(1, 50)).collect();
            let k = rng.gen_range_i32(1, 50);
            build(nums1, nums2, k)
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
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (nums1, nums2, k) = gen_case(&mut rng, mode);
        print_json(&nums1, &nums2, k);
    }
}