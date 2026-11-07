use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= values.len() <= 100_000,
        forall|k: int|
            #![trigger values[k]]
            0 <= k < values.len() ==> 1 <= values[k] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|k: int|
            #![trigger result[k]]
            0 <= k < result.len() ==> 1 <= result[k] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut v = values;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1 (constant array)
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                1 <= len <= 100_000,
                forall|j: int| #![trigger v[j]] 0 <= j < i as int ==> v[j] == 1,
                forall|j: int| #![trigger v[j]] i as int <= j < len as int ==> 1 <= v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 100_000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        v
    } else if mutation_kind == 5 && values.len() > 1 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 6 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 7 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 8 {
        // set last element to 1_000_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 9 {
        // set all elements to the first element's value
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                1 <= len <= 100_000,
                1 <= val <= 1_000_000_000,
                forall|j: int| #![trigger v[j]] 0 <= j < i as int ==> v[j] == val,
                forall|j: int| #![trigger v[j]] i as int <= j < len as int ==> 1 <= v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else {
        // fallback: identity
        values
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

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums.is_empty() || nums.len() > 100_000 { return; }
        for &v in &nums { if !(1 <= v && v <= 1_000_000_000) { return; } }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums);
        let ans = Solution::longest_subsegment_one_change_strict_inc(nums.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![7, 2, 3, 1, 5, 6], &mut seen, &mut out, &mut count);
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![5, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![5, 4, 3, 2, 1], &mut seen, &mut out, &mut count);
    emit(vec![1; 10], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000; 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 3, 2, 4, 5], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 500),
            _ => rng.gen_range_usize(500, 5000),
        };
        let max_v = match tries % 3 {
            0 => 10,
            1 => 100,
            _ => 1_000_000_000,
        };
        let nums: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        emit(nums, &mut seen, &mut out, &mut count);
    }
}

