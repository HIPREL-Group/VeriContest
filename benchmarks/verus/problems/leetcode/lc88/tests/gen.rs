use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: &mut Vec<i32>,
    m: i32,
    nums2: &mut Vec<i32>,
    n: i32,
    mutation_kind: u8,
)
    requires
        0 <= m,
        0 <= n,
        1 <= m + n <= 200,
        old(nums1).len() == (m + n) as int,
        old(nums2).len() == n as int,
        forall|i: int| 0 <= i < m as int ==>
            -1_000_000_000 <= #[trigger] old(nums1)[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < n as int ==>
            -1_000_000_000 <= #[trigger] old(nums2)[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i <= j < m as int ==>
            old(nums1)[i] <= old(nums1)[j],
        forall|i: int, j: int| 0 <= i <= j < n as int ==>
            old(nums2)[i] <= old(nums2)[j],
    ensures
        0 <= m,
        0 <= n,
        1 <= m + n <= 200,
        old(nums1).len() == (m + n) as int,
        old(nums2).len() == n as int,
        forall|i: int| 0 <= i < m as int ==>
            -1_000_000_000 <= #[trigger] old(nums1)[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < n as int ==>
            -1_000_000_000 <= #[trigger] old(nums2)[i] <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i <= j < m as int ==>
            old(nums1)[i] <= old(nums1)[j],
        forall|i: int, j: int| 0 <= i <= j < n as int ==>
            old(nums2)[i] <= old(nums2)[j],
{
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn make_sorted_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut arr: Vec<i32> = (0..len)
        .map(|_| rng.gen_range_i64(lo, hi) as i32)
        .collect();
    arr.sort();
    arr
}

fn build_nums1_nums2(sorted1: &[i32], sorted2: &[i32]) -> (Vec<i32>, i32, Vec<i32>, i32) {
    let m = sorted1.len() as i32;
    let n = sorted2.len() as i32;
    let mut nums1: Vec<i32> = sorted1.to_vec();
    nums1.resize(sorted1.len() + sorted2.len(), 0);
    let nums2: Vec<i32> = sorted2.to_vec();
    (nums1, m, nums2, n)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(88);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($s1:expr, $s2:expr, $mk:expr) => {
            if count < goal {
                let s1_val: Vec<i32> = $s1;
                let s2_val: Vec<i32> = $s2;
                let mk_val: u8 = $mk;
                let (mut nums1, m, mut nums2, n) = build_nums1_nums2(&s1_val, &s2_val);
                generate_test_case(&mut nums1, m, &mut nums2, n, mk_val);
                let nums1_input = nums1.clone();
                let nums2_input = nums2.clone();
                Solution::merge(&mut nums1, m, &mut nums2, n);
                let line = json!({
                    "input": {
                        "nums1": nums1_input,
                        "m": m,
                        "nums2": nums2_input,
                        "n": n
                    },
                    "output": nums1
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- Example test cases from description.md ----
    emit!(vec![1, 2, 3], vec![2, 5, 6], 0);
    emit!(vec![1], vec![], 0);
    emit!(vec![], vec![1], 0);

    // ---- Edge: one array empty ----
    for mk in 0u8..=4 {
        emit!(vec![5], vec![], mk);
        emit!(vec![], vec![5], mk);
        emit!(vec![-1_000_000_000], vec![], mk);
        emit!(vec![], vec![1_000_000_000], mk);
    }

    // ---- Edge: single elements ----
    for mk in 0u8..=4 {
        emit!(vec![1], vec![2], mk);
        emit!(vec![2], vec![1], mk);
        emit!(vec![0], vec![0], mk);
        emit!(vec![-1_000_000_000], vec![1_000_000_000], mk);
    }

    // ---- All same values ----
    for mk in [0u8, 2, 3] {
        emit!(vec![5, 5, 5], vec![5, 5], mk);
        emit!(vec![0, 0, 0, 0], vec![0, 0, 0, 0], mk);
    }

    // ---- Two elements each, various mutations ----
    for mk in 0u8..=4 {
        emit!(vec![1, 3], vec![2, 4], mk);
        emit!(vec![1, 2], vec![3, 4], mk);
        emit!(vec![3, 4], vec![1, 2], mk);
    }

    // ---- Small arrays with all mutations ----
    for mk in 0u8..=4 {
        emit!(vec![1, 2, 3, 4, 5], vec![2, 4, 6], mk);
        emit!(vec![-5, -3, -1], vec![-4, -2, 0, 1], mk);
    }

    // ---- Boundary values ----
    emit!(
        vec![-1_000_000_000, 0, 1_000_000_000],
        vec![-999_999_999, 999_999_999],
        0
    );
    emit!(
        vec![-1_000_000_000, -1_000_000_000],
        vec![-1_000_000_000],
        0
    );
    emit!(
        vec![1_000_000_000, 1_000_000_000],
        vec![1_000_000_000],
        0
    );

    // ---- Random tiny (m+n = 2..5), all mutations ----
    for _ in 0..5 {
        let total = rng.gen_range_usize(2, 5);
        let m = rng.gen_range_usize(0, total);
        let n = total - m;
        let s1 = make_sorted_array(&mut rng, m, -100, 100);
        let s2 = make_sorted_array(&mut rng, n, -100, 100);
        for mk in 0u8..=4 {
            emit!(s1.clone(), s2.clone(), mk);
        }
    }

    // ---- Random small (m+n = 6..20), random mutations ----
    for _ in 0..10 {
        let total = rng.gen_range_usize(6, 20);
        let m = rng.gen_range_usize(0, total);
        let n = total - m;
        let s1 = make_sorted_array(&mut rng, m, -1000, 1000);
        let s2 = make_sorted_array(&mut rng, n, -1000, 1000);
        let mk = rng.gen_range_usize(0, 4) as u8;
        emit!(s1, s2, mk);
    }

    // ---- Random medium (m+n = 21..100), random mutations ----
    for _ in 0..10 {
        let total = rng.gen_range_usize(21, 100);
        let m = rng.gen_range_usize(0, total);
        let n = total - m;
        let s1 = make_sorted_array(&mut rng, m, -1_000_000_000, 1_000_000_000);
        let s2 = make_sorted_array(&mut rng, n, -1_000_000_000, 1_000_000_000);
        let mk = rng.gen_range_usize(0, 4) as u8;
        emit!(s1, s2, mk);
    }

    // ---- Random large (m+n = 101..200), random mutations ----
    for _ in 0..5 {
        let total = rng.gen_range_usize(101, 200);
        let m = rng.gen_range_usize(0, total);
        let n = total - m;
        let s1 = make_sorted_array(&mut rng, m, -1_000_000_000, 1_000_000_000);
        let s2 = make_sorted_array(&mut rng, n, -1_000_000_000, 1_000_000_000);
        let mk = rng.gen_range_usize(0, 4) as u8;
        emit!(s1, s2, mk);
    }

    // ---- Maximum size (m+n = 200) ----
    for &(m, n) in &[(200, 0), (0, 200), (100, 100), (1, 199), (199, 1)] {
        let s1 = make_sorted_array(&mut rng, m, -1_000_000_000, 1_000_000_000);
        let s2 = make_sorted_array(&mut rng, n, -1_000_000_000, 1_000_000_000);
        emit!(s1, s2, 0);
    }

    // ---- Non-overlapping ranges ----
    emit!(vec![1, 2, 3], vec![10, 20, 30], 0);
    emit!(vec![10, 20, 30], vec![1, 2, 3], 0);

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let total = rng.gen_range_usize(1, 200);
        let m = rng.gen_range_usize(0, total);
        let n = total - m;
        let lo = rng.gen_range_i64(-1_000_000_000, 0);
        let hi = rng.gen_range_i64(0, 1_000_000_000);
        let s1 = make_sorted_array(&mut rng, m, lo, hi);
        let s2 = make_sorted_array(&mut rng, n, lo, hi);
        let mk = rng.gen_range_usize(0, 4) as u8;
        emit!(s1, s2, mk);
    }
}
