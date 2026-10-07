use vstd::prelude::*;

verus! {

pub fn generate_test_case(strs: Vec<String>, mutation_kind: u8) -> (result: Vec<String>)
    requires
        1 <= strs.len() <= 100,
        1 <= strs[0]@.len() <= 1000,
        forall |i: int| 0 <= i < strs.len() ==> #[trigger] strs[i]@.len() == strs[0]@.len(),
        forall |i: int, j: int| 0 <= i < strs.len() && 0 <= j < strs[i]@.len() ==>
            'a' <= #[trigger] strs[i]@[j] <= 'z',
    ensures
        1 <= result.len() <= 100,
        1 <= result[0]@.len() <= 1000,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i]@.len() == result[0]@.len(),
        forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i]@.len() ==>
            'a' <= #[trigger] result[i]@[j] <= 'z',
{
    if mutation_kind == 1 && strs.len() > 1 {
        // shrink: remove last row
        let mut s = strs;
        s.pop();
        s
    } else {
        // identity
        strs
    }
}

} // verus!

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

struct Solution;
include!("../code.rs");

fn make_string(chars: &[u8]) -> String {
    chars.iter().map(|&c| (b'a' + c) as char).collect()
}

fn random_strs(rng: &mut Rng, rows: usize, cols: usize) -> Vec<String> {
    let mut v = Vec::with_capacity(rows);
    for _ in 0..rows {
        let chars: Vec<u8> = (0..cols).map(|_| rng.gen_range_usize(0, 25) as u8).collect();
        v.push(make_string(&chars));
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(944);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |strs: Vec<String>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", strs);
        if !seen.insert(key) { return; }
        let output = Solution::min_deletion_size(strs.clone());
        let strs_json: Vec<&str> = strs.iter().map(|s| s.as_str()).collect();
        writeln!(out, "{}", json!({"input": {"strs": strs_json}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<String>> = vec![
        vec!["cba".into(), "daf".into(), "ghi".into()],
        vec!["a".into(), "b".into()],
        vec!["zyx".into(), "wvu".into(), "tsr".into()],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1];

    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = generate_test_case(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Seed inputs: interesting patterns
    let seed_inputs: Vec<Vec<String>> = vec![
        vec!["a".into()],                                       // single char, single row
        vec!["abc".into()],                                     // single row, multi col
        vec!["a".into(), "a".into()],                           // identical rows
        vec!["z".into(), "a".into()],                           // reversed single col
        vec!["az".into(), "za".into()],                         // one sorted col, one not
        vec!["abc".into(), "abc".into(), "abc".into()],         // all same
        vec!["aaa".into(), "bbb".into(), "ccc".into()],         // all sorted cols
        vec!["ccc".into(), "bbb".into(), "aaa".into()],         // all unsorted cols
    ];

    for s in &seed_inputs {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with diverse sizes
    while total < count {
        let (rows, cols) = match total % 5 {
            0 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),       // tiny
            1 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),     // small
            2 => (rng.gen_range_usize(5, 30), rng.gen_range_usize(5, 50)),     // medium
            3 => (rng.gen_range_usize(20, 100), rng.gen_range_usize(50, 200)), // large
            _ => (rng.gen_range_usize(50, 100), rng.gen_range_usize(200, 1000)), // max
        };
        let strs = random_strs(&mut rng, rows, cols);
        let mk = rng.gen_range_usize(0, 1) as u8;
        let result = generate_test_case(strs, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
