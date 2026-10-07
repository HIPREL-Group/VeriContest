use vstd::prelude::*;

verus! {

pub open spec fn spec_max_val() -> int {
    1000000000000000000
}

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        2 <= a.len() <= 100,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= spec_max_val(),
    ensures
        2 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= spec_max_val(),
{
    if mutation_kind == 0 {
        a
    } else if mutation_kind == 1 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1000000000000000000);
        r
    } else if mutation_kind == 3 && a[a.len() - 1] < 1000000000000000000 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] + 1);
        r
    } else if mutation_kind == 4 && a[a.len() - 1] > 1 {
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] - 1);
        r
    } else if mutation_kind == 5 && a.len() < 100 {
        let mut r = a;
        r.push(1);
        r
    } else if mutation_kind == 6 && a.len() > 2 {
        let mut r = a;
        r.pop();
        r
    } else if mutation_kind == 7 {
        let mut r = a;
        r.set(0, 1);
        r
    } else if mutation_kind == 8 {
        let val = a[0];
        let n = a.len();
        let mut r = a;
        let mut i: usize = 0;
        while i < n
            invariant
                n == r.len(),
                2 <= n <= 100,
                0 <= i <= n,
                1 <= val <= spec_max_val(),
                forall|j: int| 0 <= j < i ==> r[j] == val,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= spec_max_val(),
                forall|j: int| i <= j < n ==> r[j] == a[j],
            decreases n - i,
        {
            r.set(i, val);
            i = i + 1;
        }
        r
    } else if mutation_kind == 9 && a.len() >= 4 {
        let mut r = a;
        let tmp = r[0];
        r.set(0, r[1]);
        r.set(1, tmp);
        r
    } else {
        a
    }
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    let max_val: i64 = 1_000_000_000_000_000_000;
    let mut a = Vec::with_capacity(len);
    for _ in 0..len {
        a.push(rng.gen_range_i64(1, max_val));
    }
    a
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", a);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::paint_the_array(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": output})).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![10, 5, 15],
        vec![100, 10, 200],
        vec![9, 8, 2, 6, 6, 2, 8, 6, 5, 4],
        vec![1, 3],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(generate_test_case(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    let seeds: Vec<Vec<i64>> = vec![
        vec![1, 1],
        vec![1_000_000_000_000_000_000, 1_000_000_000_000_000_000],
        vec![1, 1_000_000_000_000_000_000],
        vec![2, 3, 2, 3],
        vec![6, 3, 6, 3, 6],
        vec![1, 2, 1, 2, 1, 2],
        vec![4, 4, 4, 4],
        vec![2, 4, 2, 4, 2],
    ];

    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(generate_test_case(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 60),
            _ => rng.gen_range_usize(61, 100),
        };
        let a = random_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(generate_test_case(a, mk), &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
