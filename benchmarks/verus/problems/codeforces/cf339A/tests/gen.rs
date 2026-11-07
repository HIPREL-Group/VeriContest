use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<u8>) -> (result: Vec<u8>)
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 3,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 50 { 50usize } else { values.len() };
    let limit = 3;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 50,
            limit == 3,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub open spec fn input_digits_valid(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> 1 <= #[trigger] seq[i] as int <= 3
}

pub fn generate_candidate(
    nums: Vec<u8>,
    mutation_kind: u8,
) -> (result: Vec<u8>)
    requires
        1 <= nums.len() <= 99,
        input_digits_valid(nums@),
    ensures
        1 <= result.len() <= 100,
        input_digits_valid(result@),
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() < 100 {
        // grow: push a 1
        let mut d = nums;
        d.push(1u8);
        d
    } else if mutation_kind == 2 && nums.len() > 1 {
        // shrink: pop last
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 99,
                forall|j: int| 0 <= j < i ==> d[j] == 1u8,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 3,
            decreases d.len() - i,
        {
            d.set(i, 1u8);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 3
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 99,
                forall|j: int| 0 <= j < i ==> d[j] == 3u8,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 3,
            decreases d.len() - i,
        {
            d.set(i, 3u8);
            i += 1;
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 2
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 99,
                forall|j: int| 0 <= j < i ==> d[j] == 2u8,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] as int <= 3,
            decreases d.len() - i,
        {
            d.set(i, 2u8);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // nudge first element: if < 3, increment
        let mut d = nums;
        if d[0] < 3 {
            d.set(0, (d[0] + 1) as u8);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first element: if > 1, decrement
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, (d[0] - 1) as u8);
        }
        d
    } else if mutation_kind == 8 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1u8);
        d
    } else if mutation_kind == 9 {
        // set first element to 3 (max boundary)
        let mut d = nums;
        d.set(0, 3u8);
        d
    } else if mutation_kind == 10 && nums.len() < 100 {
        // grow: push a 2
        let mut d = nums;
        d.push(2u8);
        d
    } else if mutation_kind == 11 && nums.len() < 100 {
        // grow: push a 3
        let mut d = nums;
        d.push(3u8);
        d
    } else {
        // fallback: identity
        nums
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

fn mutate(nums: Vec<u8>, mk: u8) -> Vec<u8> {
    if mk == 0 {
        nums
    } else if mk == 1 && nums.len() < 100 {
        let mut d = nums; d.push(1); d
    } else if mk == 2 && nums.len() > 1 {
        let mut d = nums; d.pop(); d
    } else if mk == 3 {
        let mut d = nums; for i in 0..d.len() { d[i] = 1; } d
    } else if mk == 4 {
        let mut d = nums; for i in 0..d.len() { d[i] = 3; } d
    } else if mk == 5 {
        let mut d = nums; for i in 0..d.len() { d[i] = 2; } d
    } else if mk == 6 {
        let mut d = nums; if d[0] < 3 { d[0] += 1; } d
    } else if mk == 7 {
        let mut d = nums; if d[0] > 1 { d[0] -= 1; } d
    } else if mk == 8 {
        let mut d = nums; d[0] = 1; d
    } else if mk == 9 {
        let mut d = nums; d[0] = 3; d
    } else if mk == 10 && nums.len() < 100 {
        let mut d = nums; d.push(2); d
    } else if mk == 11 && nums.len() < 100 {
        let mut d = nums; d.push(3); d
    } else {
        nums
    }
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<u8> {
    (0..len).map(|_| rng.gen_range_usize(1, 3) as u8).collect()
}

fn build_input(nums: &[u8]) -> String {
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join("+");
    s.push('\n');
    s
}

fn build_output(sorted: &[u8]) -> String {
    let parts: Vec<String> = sorted.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join("+");
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(339);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<u8>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums.is_empty() || nums.len() > 100 { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let nums = generate_test_case(nums);
        let inp = build_input(&nums);
        let sorted = Solution::sort_digits(nums.clone());
        let outs = build_output(&sorted);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![3, 2, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 3, 1, 3, 2], &mut seen, &mut out, &mut count);

    let seed_nums: Vec<Vec<u8>> = vec![
        vec![1], vec![2], vec![3], vec![1, 2, 3], vec![3, 2, 1],
        vec![1, 1, 1], vec![2, 2, 2], vec![3, 3, 3],
        vec![1, 3], vec![2, 1], vec![3, 1, 2], vec![1, 2, 1, 3, 2, 3],
    ];

    for nums in &seed_nums {
        for mk in 0..=11u8 {
            let r = mutate(nums.clone(), mk);
            emit(r, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 99),
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let r = mutate(nums, mk);
        emit(r, &mut seen, &mut out, &mut count);
    }
}
