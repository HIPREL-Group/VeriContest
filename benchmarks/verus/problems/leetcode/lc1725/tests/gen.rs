use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 1000000000 && 1 <= result[i][1] <= 1000000000,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result[i])[0] != result[i][1],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;

    while i < count
        invariant
            1 <= count <= 1000, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 1000000000 && 1 <= result[j][1] <= 1000000000,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j][0] != result[j][1],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 1000000000 { 1000000000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 1000000000 { 1000000000 } else { b };
        if a == b { b = if a < 1000000000 { a + 1 } else { 1 }; }
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    result
}


pub fn generate_candidate(ls: Vec<i32>, ws: Vec<i32>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= ls.len() <= 1000,
        ls.len() == ws.len(),
        forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < ws.len() ==> 1 <= #[trigger] ws[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==>
            (#[trigger] result[i]).len() == 2,
        forall|i: int| 0 <= i < result.len() ==>
            1 <= (#[trigger] result[i])[0] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.len() ==>
            1 <= (#[trigger] result[i])[1] <= 1_000_000_000,
{
    let n = ls.len();
    let mut rects: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;

    if mutation_kind == 1 {
        // Swap l and w for every rectangle
        while idx < n
            invariant
                n == ls.len(), n == ws.len(), 1 <= n <= 1000,
                0 <= idx <= n, rects.len() == idx,
                forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
                forall|i: int| 0 <= i < ws.len() ==> 1 <= #[trigger] ws[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(ws[idx]);
            pair.push(ls[idx]);
            rects.push(pair);
            idx += 1;
        }
    } else if mutation_kind == 2 && n >= 2 {
        // Set first rectangle length to 1 (minimum boundary)
        while idx < n
            invariant
                n == ls.len(), n == ws.len(), 1 <= n <= 1000, n >= 2,
                0 <= idx <= n, rects.len() == idx,
                forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
                forall|i: int| 0 <= i < ws.len() ==> 1 <= #[trigger] ws[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            let l_val = if idx == 0 { 1i32 } else { ls[idx] };
            pair.push(l_val);
            pair.push(ws[idx]);
            rects.push(pair);
            idx += 1;
        }
    } else if mutation_kind == 3 {
        // Set all widths to 1_000_000_000 (max boundary)
        while idx < n
            invariant
                n == ls.len(), n == ws.len(), 1 <= n <= 1000,
                0 <= idx <= n, rects.len() == idx,
                forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(ls[idx]);
            pair.push(1_000_000_000i32);
            rects.push(pair);
            idx += 1;
        }
    } else if mutation_kind == 4 {
        // Make all rectangles identical (use first element values)
        while idx < n
            invariant
                n == ls.len(), n == ws.len(), 1 <= n <= 1000,
                0 <= idx <= n, rects.len() == idx,
                forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
                forall|i: int| 0 <= i < ws.len() ==> 1 <= #[trigger] ws[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(ls[0]);
            pair.push(ws[0]);
            rects.push(pair);
            idx += 1;
        }
    } else if mutation_kind == 5 {
        // Set all lengths and widths to 1 (minimum square)
        while idx < n
            invariant
                n == ls.len(), 1 <= n <= 1000,
                0 <= idx <= n, rects.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(1i32);
            pair.push(1i32);
            rects.push(pair);
            idx += 1;
        }
    } else {
        // Identity (mutation_kind == 0 or fallback): build rectangles as-is
        while idx < n
            invariant
                n == ls.len(), n == ws.len(), 1 <= n <= 1000,
                0 <= idx <= n, rects.len() == idx,
                forall|i: int| 0 <= i < ls.len() ==> 1 <= #[trigger] ls[i] <= 1_000_000_000,
                forall|i: int| 0 <= i < ws.len() ==> 1 <= #[trigger] ws[i] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] rects[j]).len() == 2,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[0] <= 1_000_000_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= (#[trigger] rects[j])[1] <= 1_000_000_000,
            decreases n - idx,
        {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(ls[idx]);
            pair.push(ws[idx]);
            rects.push(pair);
            idx += 1;
        }
    }
    rects
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn build_vecs(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut ls = Vec::with_capacity(n);
    let mut ws = Vec::with_capacity(n);
    for _ in 0..n {
        ls.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
        ws.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    (ls, ws)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1725);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |rects: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let rects = generate_test_case(rects);
        if *count >= target {
            return;
        }
        let key = format!("{:?}", rects);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_good_rectangles(rects.clone());
        writeln!(out, "{}", json!({"input": {"rectangles": rects}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let ex1 = vec![vec![5, 8], vec![3, 9], vec![5, 12], vec![16, 5]];
    emit(ex1, &mut seen, &mut out, &mut count);
    let ex2 = vec![vec![2, 3], vec![3, 7], vec![4, 3], vec![3, 7]];
    emit(ex2, &mut seen, &mut out, &mut count);

    // Hand-crafted seed inputs
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1_000_000_000], vec![1_000_000_000]),
        (vec![1, 1], vec![1, 1]),
        (vec![5, 5, 5], vec![5, 5, 5]),
        (vec![1, 2, 3], vec![3, 2, 1]),
        (vec![10, 20, 30, 40], vec![40, 30, 20, 10]),
        (vec![1_000_000_000, 1], vec![1, 1_000_000_000]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for (ls, ws) in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_candidate(ls.clone(), ws.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across diverse size classes
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let (ls, ws) = build_vecs(&mut rng, n);
        let mk = rng.gen_range_usize(0, 5) as u8;
        let result = generate_candidate(ls, ws, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
