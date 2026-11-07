use vstd::prelude::*;

verus! {

// Spec fn helpers from spec.rs
pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
    recommends
        0 <= end <= nums.len(),
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum(nums, end - 1) + nums[end - 1] as int
    }
}

pub open spec fn total_sum(nums: Seq<i64>) -> int {
    prefix_sum(nums, nums.len() as int)
}

proof fn lemma_prefix_sum_upper_bound(nums: Seq<i64>, end: int)
    requires
        0 <= end <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] as int <= 1_000_000_000,
    ensures
        prefix_sum(nums, end) <= end * 1_000_000_000,
    decreases end,
{
    if end > 0 {
        lemma_prefix_sum_upper_bound(nums, end - 1);
    }
}

pub fn generate_test_case(
    a: Vec<i64>,
    b: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= a.len() <= 300_000,
        1 <= b.len() <= 300_000,
        forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int && (a[x] as int) <= 1_000_000_000,
        forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int && (b[x] as int) <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 300_000,
        1 <= result.1.len() <= 300_000,
        forall|x: int| 0 <= x < result.0.len() ==> 1 <= #[trigger] result.0[x] as int && (result.0[x] as int) <= 1_000_000_000,
        forall|x: int| 0 <= x < result.1.len() ==> 1 <= #[trigger] result.1[x] as int && (result.1[x] as int) <= 1_000_000_000,
        total_sum(result.0@) <= i64::MAX,
        total_sum(result.1@) <= i64::MAX,
{
    let mut ra = a;
    let mut rb = b;

    if mutation_kind == 1 {
        // set first element of a to 1
        ra.set(0, 1);
    } else if mutation_kind == 2 {
        // set first element of b to 1
        rb.set(0, 1);
    } else if mutation_kind == 3 && ra.len() < 300_000 {
        // grow a by appending 1
        ra.push(1);
    } else if mutation_kind == 4 && rb.len() < 300_000 {
        // grow b by appending 1
        rb.push(1);
    } else if mutation_kind == 5 && ra.len() > 1 {
        // shrink a by removing last element
        ra.pop();
    } else if mutation_kind == 6 && rb.len() > 1 {
        // shrink b by removing last element
        rb.pop();
    } else if mutation_kind == 7 {
        // set last element of a to max value
        let last = ra.len() - 1;
        ra.set(last, 1_000_000_000);
    } else if mutation_kind == 8 {
        // set last element of b to max value
        let last = rb.len() - 1;
        rb.set(last, 1_000_000_000);
    }
    // else: identity (mutation_kind == 0 or fallback)

    proof {
        lemma_prefix_sum_upper_bound(ra@, ra.len() as int);
        lemma_prefix_sum_upper_bound(rb@, rb.len() as int);
        assert(ra.len() as int * 1_000_000_000 <= 300_000 * 1_000_000_000);
        assert(rb.len() as int * 1_000_000_000 <= 300_000 * 1_000_000_000);
        assert(300_000 * 1_000_000_000 <= i64::MAX as int);
    }

    (ra, rb)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
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

fn build_input(a: &[i64], b: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let pa: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&pa.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", b.len()));
    let pb: Vec<String> = b.iter().map(|x| x.to_string()).collect();
    s.push_str(&pb.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, b: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        h ^= b.len() as u64;
        for &x in &b { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a, &b);
        let ans = Solution::max_equal_block_count(a, b);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![11,2,3,5,7], vec![11,7,3,7], &mut seen, &mut out, &mut count);
    emit(vec![1,2,3], vec![1,2,3], &mut seen, &mut out, &mut count);
    emit(vec![1,2,3], vec![1,5], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1], vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1], vec![2], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1], vec![1,1,1], &mut seen, &mut out, &mut count);
    emit(vec![10], vec![1,2,3,4], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,1], vec![2,2], &mut seen, &mut out, &mut count);

    // Random tests with matching sums
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(5, 30),
            3 => rng.gen_range_usize(20, 100),
            _ => rng.gen_range_usize(50, 500),
        };
        let m = match count % 3 {
            0 => n,
            1 => rng.gen_range_usize(1, n.max(2)),
            _ => rng.gen_range_usize(1, (n*2).max(2)),
        };
        let max_val = match count % 4 {
            0 => 10i64,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000_000,
        };
        let a = random_array(&mut rng, n, max_val);
        let b = random_array(&mut rng, m, max_val);
        emit(a, b, &mut seen, &mut out, &mut count);
    }
}

