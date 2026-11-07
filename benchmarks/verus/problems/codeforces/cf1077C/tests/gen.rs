use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: (usize, Vec<i32>))
    requires
        2 <= values.len() <= 200_000,
        forall|i: int| 0 <= i && i < values.len() ==> 1 <= #[trigger] values@[i] && values@[i] <= 1_000_000,
    ensures
        2 <= result.0 && result.0 <= 200_000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= #[trigger] result.1@[i] && result.1@[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        let n = values.len();
        (n, values)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 2 {
        // set first element to 1_000_000 (max boundary)
        let mut v = values;
        v.set(0, 1_000_000);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 3 {
        // set all elements to the first element's value
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                2 <= len <= 200_000,
                1 <= val <= 1_000_000,
                forall|j: int| 0 <= j && j < i ==> #[trigger] v@[j] == val,
                forall|j: int| i <= j && j < len ==> #[trigger] v@[j] == values@[j],
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        (len, v)
    } else if mutation_kind == 4 && values.len() < 200_000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 5 && values.len() > 2 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        let n = v.len();
        (n, v)
    } else if mutation_kind == 6 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 7 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        let n = v.len();
        (n, v)
    } else if mutation_kind == 8 {
        // set last element to 1_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000);
        let n = v.len();
        (n, v)
    } else {
        // fallback: identity
        let n = values.len();
        (n, values)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(res: &[i32]) -> String {
    let mut s = format!("{}\n", res.len());
    if !res.is_empty() {
        let parts: Vec<String> = res.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_array(rng: &mut Rng, len: usize, max_val: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i32(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let res = Solution::nice_indices(a.len(), a.clone());
        let outs = build_output(&res);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![2,5,1,2,2], &mut seen, &mut out, &mut count);
    emit(vec![8,3,5,2], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1,1], &mut seen, &mut out, &mut count);
    emit(vec![1,2], &mut seen, &mut out, &mut count);
    emit(vec![5,5,5,5,5], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,2], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000,1_000_000], &mut seen, &mut out, &mut count);

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 1000),
        };
        let max_val = match count % 4 {
            0 => 10i32,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

