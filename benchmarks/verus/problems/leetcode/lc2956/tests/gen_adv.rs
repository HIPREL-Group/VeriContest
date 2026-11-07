use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1.len() <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
{
    (bounded_values(&nums1), bounded_values(&nums2))
}


pub fn generate_candidate(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100,
        1 <= nums2.len() <= 100,
        forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 100,
        forall|i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 100,
    ensures
        result.0.len() == nums1.len(),
        result.1.len() == nums2.len(),
        result.0.len() <= 2147483647usize,
        result.1.len() <= 2147483647usize,
{
    (nums1, nums2)
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_const_vec(len: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(val);
    }
    v
}

fn pick_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 5);
            let m = rng.gen_range_usize(1, 5);
            (make_vec(rng, n, 1, 10), make_vec(rng, m, 1, 10))
        }
        1 => {
            // completely disjoint ranges
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            let a = make_vec(rng, n, 1, 50);
            let b = make_vec(rng, m, 51, 100);
            (a, b)
        }
        2 => {
            // identical vectors
            let n = rng.gen_range_usize(1, 100);
            let v = make_vec(rng, n, 1, 100);
            (v.clone(), v)
        }
        3 => {
            // all same value, both containing it
            let val = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            (make_const_vec(n, val), make_const_vec(m, val))
        }
        4 => {
            // all same value, different
            let v1 = rng.gen_range_i32(1, 50);
            let v2 = rng.gen_range_i32(51, 100);
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            (make_const_vec(n, v1), make_const_vec(m, v2))
        }
        5 => {
            // single-element
            (vec![rng.gen_range_i32(1, 100)], vec![rng.gen_range_i32(1, 100)])
        }
        6 => {
            // max size, narrow range (many overlaps)
            (make_vec(rng, 100, 1, 5), make_vec(rng, 100, 1, 5))
        }
        7 => {
            // max size, wide range
            (make_vec(rng, 100, 1, 100), make_vec(rng, 100, 1, 100))
        }
        8 => {
            // boundary values
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 100);
            let mut a = Vec::with_capacity(n);
            let mut b = Vec::with_capacity(m);
            for _ in 0..n {
                a.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 });
            }
            for _ in 0..m {
                b.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 });
            }
            (a, b)
        }
        9 => {
            // one big, one small
            (make_vec(rng, 100, 1, 100), vec![rng.gen_range_i32(1, 100)])
        }
        _ => {
            // small, one big
            (vec![rng.gen_range_i32(1, 100)], make_vec(rng, 100, 1, 100))
        }
    }
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    let (nums1, nums2) = generate_test_case(nums1.to_vec(), nums2.to_vec());
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums2[i]);
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
        let (n1, n2) = pick_case(&mut rng, mode);
        let (a, b) = generate_candidate(n1, n2);
        print_json(&a, &b);
    }
}
