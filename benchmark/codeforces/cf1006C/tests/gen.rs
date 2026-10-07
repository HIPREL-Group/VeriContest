use vstd::prelude::*;

verus! {

// Spec fn helpers copied from spec.rs (standalone, without Self::)

pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
    recommends 0 <= end <= nums.len(),
    decreases end,
{
    if end <= 0 { 0 }
    else { prefix_sum(nums, end - 1) + nums[end - 1] as int }
}

pub open spec fn total_sum(nums: Seq<i64>) -> int {
    prefix_sum(nums, nums.len() as int)
}

// Lemma: prefix_sum bounded by end * max_element_value
proof fn prefix_sum_upper_bound(nums: Seq<i64>, end: int, max_val: int)
    requires
        0 <= end <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> nums[k] as int <= max_val,
        max_val >= 0,
    ensures
        prefix_sum(nums, end) <= end * max_val,
    decreases end,
{
    if end > 0 {
        prefix_sum_upper_bound(nums, end - 1, max_val);
        assert(nums[end - 1] as int <= max_val);
        assert((end - 1) * max_val + max_val == end * max_val) by (nonlinear_arith)
            requires max_val >= 0, end > 0;
    }
}

// Lemma: prefix_sum is non-negative when elements >= 1
proof fn prefix_sum_non_negative(nums: Seq<i64>, end: int)
    requires
        0 <= end <= nums.len(),
        forall|k: int| 0 <= k < nums.len() ==> 1 <= nums[k] as int,
    ensures
        prefix_sum(nums, end) >= 0,
    decreases end,
{
    if end > 0 {
        prefix_sum_non_negative(nums, end - 1);
    }
}

fn prove_total_sum_bound(nums: &Vec<i64>)
    requires
        nums.len() <= 200_000,
        forall|k: int| 0 <= k < nums.len()
            ==> 1 <= #[trigger] nums[k] as int && (nums[k] as int) <= 1_000_000_000,
    ensures
        total_sum(nums@) <= i64::MAX,
{
    proof {
        prefix_sum_upper_bound(nums@, nums@.len() as int, 1_000_000_000);
        // 200_000 * 1_000_000_000 = 200_000_000_000_000 <= 9_223_372_036_854_775_807 = i64::MAX
        assert(nums@.len() as int * 1_000_000_000 <= 200_000 * 1_000_000_000int);
        assert(200_000 * 1_000_000_000int <= i64::MAX as int);
    }
}

pub fn generate_test_case(
    elems: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= elems.len() <= 200_000,
        forall|k: int| 0 <= k < elems.len()
            ==> 1 <= #[trigger] elems[k] as int && (elems[k] as int) <= 1_000_000_000,
    ensures
        1 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len()
            ==> 1 <= #[trigger] result[k] as int && (result[k] as int) <= 1_000_000_000,
        total_sum(result@) <= i64::MAX,
{
    if mutation_kind == 0 {
        // identity
        prove_total_sum_bound(&elems);
        elems
    } else if mutation_kind == 1 && elems.len() < 200_000 {
        // grow: append element with value 1
        let mut d = elems;
        d.push(1);
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 2 && elems.len() > 1 {
        // shrink: remove last element
        let mut d = elems;
        d.pop();
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 3 {
        // set first element to 1 (minimum boundary)
        let mut d = elems;
        d.set(0, 1);
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 4 {
        // set first element to max boundary
        let mut d = elems;
        d.set(0, 1_000_000_000);
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1);
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 6 {
        // set last element to max boundary
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i <= j < d.len()
                    ==> 1 <= #[trigger] d[j] as int && (d[j] as int) <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 8 {
        // set all elements to max boundary
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i64,
                forall|j: int| i <= j < d.len()
                    ==> 1 <= #[trigger] d[j] as int && (d[j] as int) <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        prove_total_sum_bound(&d);
        d
    } else if mutation_kind == 9 && elems.len() >= 2 {
        // swap first and last elements
        let mut d = elems;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        prove_total_sum_bound(&d);
        d
    } else {
        // fallback: identity
        prove_total_sum_bound(&elems);
        elems
    }
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

fn build_input(nums: &[i64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
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
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums);
        let ans = Solution::max_equal_outer_sum(nums.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<i64>> = vec![
        vec![1, 3, 1, 1, 4],
        vec![1, 3, 2, 1, 4],
        vec![4, 1, 2],
    ];
    for e in examples { emit(e, &mut seen, &mut out, &mut count); }

    let edge_cases: Vec<Vec<i64>> = vec![
        vec![1],
        vec![1, 1],
        vec![1_000_000_000],
        vec![1, 1, 1, 1, 1],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 1_000_000_000, 1],
        vec![1_000_000_000, 1_000_000_000],
        vec![2, 2],
        vec![3, 3, 3],
        vec![1, 2, 1],
        vec![5, 1, 5],
        vec![10, 20, 10],
        vec![1, 1, 2, 2, 1, 1],
    ];
    for ec in edge_cases { emit(ec, &mut seen, &mut out, &mut count); }

    while count < target {
        let n = match count % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 15),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(20, 100),
            4 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(100, 500),
        };
        let max_val = match count % 4 {
            0 => 10i64,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

