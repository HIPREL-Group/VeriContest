use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: Vec<i64>,
    m_val: usize,
    k_val: usize,
    mutation_kind: u8,
) -> (result: (Vec<i64>, usize, usize))
    requires
        1 <= values.len() <= 5000,
        1 <= m_val <= values.len(),
        1 <= k_val,
        m_val * k_val <= values.len(),
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 5000,
        1 <= result.1 <= result.0.len(),
        1 <= result.2,
        result.1 * result.2 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (values, m_val, k_val)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut v = values;
        v.set(0, 0);
        (v, m_val, k_val)
    } else if mutation_kind == 2 {
        // set first element to max
        let mut v = values;
        v.set(0, 1_000_000_000);
        (v, m_val, k_val)
    } else if mutation_kind == 3 {
        // set all elements to values[0]
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                1 <= len <= 5000,
                0 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j && j < i as int ==> #[trigger] v[j] == val,

                forall|j: int| 0 <= j && j < len as int ==> 0 <= #[trigger] v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        (v, m_val, k_val)
    } else if mutation_kind == 4 {
        // set all elements to 0
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                1 <= len <= 5000,
                forall|j: int| 0 <= j && j < i as int ==> #[trigger] v[j] == 0,

                forall|j: int| 0 <= j && j < len as int ==> 0 <= #[trigger] v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, 0);
            i += 1;
        }
        (v, m_val, k_val)
    } else if mutation_kind == 5 {
        // set all elements to max
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                1 <= len <= 5000,
                forall|j: int| 0 <= j && j < i as int ==> #[trigger] v[j] == 1_000_000_000,

                forall|j: int| 0 <= j && j < len as int ==> 0 <= #[trigger] v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, 1_000_000_000);
            i += 1;
        }
        (v, m_val, k_val)
    } else if mutation_kind == 6 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (v, m_val, k_val)
    } else if mutation_kind == 7 {
        // set last element to 0
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 0);
        (v, m_val, k_val)
    } else if mutation_kind == 8 {
        // set last element to max
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        (v, m_val, k_val)
    } else {
        // fallback: identity
        (values, m_val, k_val)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

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

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn random_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1_000_000_000));
    }
    arr
}

fn build_input(nums: &[i64], m: usize, k: usize) -> String {
    let n = nums.len();
    let mut s = format!("{} {} {}\n", n, m, k);
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i128) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(467);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, m: usize, k: usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if nums.is_empty() || m == 0 || k == 0 || m * k > nums.len() { return; }
        let key = format!("{:?}_{}_{}", nums, m, k);
        if !seen.insert(key) { return; }
        let result = Solution::max_k_segments_sum(nums.clone(), m, k);
        let inp = build_input(&nums, m, k);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![1, 2, 3, 4, 5], 2, 1, &mut seen, &mut out, &mut count);
    emit(vec![2, 10, 7, 18, 5, 33, 0], 1, 3, &mut seen, &mut out, &mut count);

    // Hand-crafted edges
    let edge_cases: Vec<(Vec<i64>, usize, usize)> = vec![
        (vec![0], 1, 1),
        (vec![1_000_000_000], 1, 1),
        (vec![5, 5], 1, 2),
        (vec![5, 5], 2, 1),
        (vec![1, 2, 3], 1, 3),
        (vec![1, 2, 3, 4, 5, 6], 2, 3),
        (vec![1, 2, 3, 4, 5, 6], 3, 2),
        (vec![0, 0, 0, 0, 0], 2, 2),
        (vec![1_000_000_000; 10], 2, 3),
        (vec![1; 100], 5, 10),
        (vec![1_000_000_000; 50], 5, 5),
    ];

    for (nums, m, k) in &edge_cases {
        emit(nums.clone(), *m, *k, &mut seen, &mut out, &mut count);
    }

    // Random test cases across size classes (smaller for speed since DP is O(n*k))
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 2000),
        };
        let arr = random_array(&mut rng, n);
        let m = rng.gen_range_usize(1, n);
        let max_k = n / m;
        let k = rng.gen_range_usize(1, max_k);
        emit(arr, m, k, &mut seen, &mut out, &mut count);
    }
}

