use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 1000,
        1 <= nums2.len() <= 1000,
        forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
        forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
{
    (nums1, nums2)
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_array(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_i32(lo, hi));
    }
    v
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let n1 = rng.gen_usize(1, 10);
            let n2 = rng.gen_usize(1, 10);
            (build_array(rng, n1, 0, 1000), build_array(rng, n2, 0, 1000))
        }
        1 => {
            // both length 1
            (vec![rng.gen_i32(0, 1000)], vec![rng.gen_i32(0, 1000)])
        }
        2 => {
            // identical arrays
            let n = rng.gen_usize(1, 50);
            let a = build_array(rng, n, 0, 1000);
            let b = a.clone();
            (a, b)
        }
        3 => {
            // no intersection: nums1 all small, nums2 all large
            let n1 = rng.gen_usize(1, 100);
            let n2 = rng.gen_usize(1, 100);
            (build_array(rng, n1, 0, 100), build_array(rng, n2, 500, 1000))
        }
        4 => {
            // all duplicates same value
            let n1 = rng.gen_usize(1, 1000);
            let n2 = rng.gen_usize(1, 1000);
            let v1 = rng.gen_i32(0, 1000);
            let v2 = rng.gen_i32(0, 1000);
            (vec![v1; n1], vec![v2; n2])
        }
        5 => {
            // max size
            (build_array(rng, 1000, 0, 1000), build_array(rng, 1000, 0, 1000))
        }
        6 => {
            // boundary values 0 and 1000
            let n1 = rng.gen_usize(1, 50);
            let n2 = rng.gen_usize(1, 50);
            let mut a = Vec::with_capacity(n1);
            let mut b = Vec::with_capacity(n2);
            for _ in 0..n1 { a.push(if rng.next_u64() % 2 == 0 {0} else {1000}); }
            for _ in 0..n2 { b.push(if rng.next_u64() % 2 == 0 {0} else {1000}); }
            (a, b)
        }
        7 => {
            // small domain = many duplicates
            let n1 = rng.gen_usize(1, 200);
            let n2 = rng.gen_usize(1, 200);
            (build_array(rng, n1, 0, 5), build_array(rng, n2, 0, 5))
        }
        8 => {
            // subset
            let n = rng.gen_usize(1, 100);
            let a = build_array(rng, n, 0, 1000);
            let mut b = a.clone();
            for _ in 0..rng.gen_usize(0, 10) {
                b.push(rng.gen_i32(0, 1000));
                if b.len() >= 1000 { break; }
            }
            (a, b)
        }
        9 => {
            // one very small, one max
            (vec![rng.gen_i32(0, 1000)], build_array(rng, 1000, 0, 1000))
        }
        _ => {
            let n1 = rng.gen_usize(1, 500);
            let n2 = rng.gen_usize(1, 500);
            (build_array(rng, n1, 0, 1000), build_array(rng, n2, 0, 1000))
        }
    }
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
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
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (n1, n2) = gen_mode(&mut rng, mode);
        let (a, b) = generate_test_case(n1, n2);
        print_json(&a, &b);
    }
}