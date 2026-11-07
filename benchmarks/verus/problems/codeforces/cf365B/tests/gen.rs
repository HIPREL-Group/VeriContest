use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to 0 (min boundary)
        let mut v = values;
        v.set(0, 0);
        v
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut v = values;
        v.set(0, 1_000_000_000);
        v
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
                1 <= len <= 100_000,
                0 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> #[trigger] v[j] == val,
                forall|j: int| i as int <= j < len ==> 0 <= #[trigger] v[j] <= 1_000_000_000,
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 100_000 {
        // grow by one element (push 0)
        let mut v = values;
        v.push(0);
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
        // set last element to 0 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 0);
        v
    } else if mutation_kind == 8 {
        // set last element to 1_000_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 9 && values.len() >= 3 {
        // make a fibonacci segment: set v[2] = v[0] + v[1] (if in range)
        let a = values[0];
        let b = values[1];
        let s = a + b;
        if s <= 1_000_000_000 {
            let mut v = values;
            v.set(2, s);
            v
        } else {
            values
        }
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

fn mutate(values: Vec<i64>, mk: u8) -> Vec<i64> {
    if mk == 0 {
        values
    } else if mk == 1 {
        let mut v = values; v[0] = 0; v
    } else if mk == 2 {
        let mut v = values; v[0] = 1_000_000_000; v
    } else if mk == 3 {
        let val = values[0];
        let mut v = values;
        for i in 1..v.len() { v[i] = val; }
        v
    } else if mk == 4 && values.len() < 100_000 {
        let mut v = values; v.push(0); v
    } else if mk == 5 && values.len() > 1 {
        let mut v = values; v.pop(); v
    } else if mk == 6 && values.len() >= 2 {
        let mut v = values; let a = v[0]; let b = v[1]; v[0] = b; v[1] = a; v
    } else if mk == 7 {
        let mut v = values; let last = v.len() - 1; v[last] = 0; v
    } else if mk == 8 {
        let mut v = values; let last = v.len() - 1; v[last] = 1_000_000_000; v
    } else if mk == 9 && values.len() >= 3 {
        let a = values[0]; let b = values[1]; let s = a + b;
        if s <= 1_000_000_000 {
            let mut v = values; v[2] = s; v
        } else {
            values
        }
    } else {
        values
    }
}

fn random_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(0, 1_000_000_000)).collect()
}

fn build_input(nums: &[i64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(365);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums.is_empty() || nums.len() > 100_000 { return; }
        for &n in &nums { if !(0 <= n && n <= 1_000_000_000) { return; } }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums);
        let ans = Solution::longest_fibonacci_segment(nums.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 5, 8, 13, 21, 34, 55, 89],
        vec![1, 1, 1, 1, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    let seeds: Vec<Vec<i64>> = vec![
        vec![0],
        vec![0, 0],
        vec![1, 1, 2, 3, 5, 8],
        vec![1_000_000_000],
        vec![0, 1_000_000_000],
        vec![500_000_000, 500_000_000, 1_000_000_000],
        vec![1, 1, 2, 3, 5, 8, 13, 21],
        vec![5, 5, 5, 5, 5],
        vec![1, 2, 4, 8, 16],
        vec![0, 0, 0, 0, 0],
        vec![1, 0, 1, 1, 2, 3],
        vec![3, 7, 2, 5, 1],
    ];
    for s in &seeds {
        for mk in 0..=9u8 {
            let nums = mutate(s.clone(), mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![(1, 5), (6, 20), (21, 100), (101, 500), (501, 1000)];
    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(*lo, *hi);
            let arr = random_array(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let nums = mutate(arr, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let len = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let arr = random_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let nums = mutate(arr, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}

