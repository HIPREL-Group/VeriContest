use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i32>,
    b: Vec<i32>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i32>, Vec<i32>))
    requires
        1 <= a.len() && a.len() <= 50000,
        b.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> 0 <= a[i] && a[i] <= 1000000000,
        forall|i: int| 0 <= i && i < b.len() ==> 0 <= b[i] && b[i] <= 1000000000,
    ensures
        1 <= result.0 && result.0 <= 50000,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> 0 <= result.1@[i] && result.1@[i] <= 1000000000,
        forall|i: int| 0 <= i && i < result.0 ==> 0 <= result.2@[i] && result.2@[i] <= 1000000000,
{
    let n = a.len();
    if mutation_kind == 0 {
        // identity
        (n, a, b)
    } else if mutation_kind == 1 {
        // set first element of a to 0
        let mut da = a;
        da.set(0, 0);
        (n, da, b)
    } else if mutation_kind == 2 {
        // set first element of a to 1000000000
        let mut da = a;
        da.set(0, 1000000000);
        (n, da, b)
    } else if mutation_kind == 3 {
        // set first element of b to 0
        let mut db = b;
        db.set(0, 0);
        (n, a, db)
    } else if mutation_kind == 4 {
        // set first element of b to 1000000000
        let mut db = b;
        db.set(0, 1000000000);
        (n, a, db)
    } else if mutation_kind == 5 {
        // set all elements of a to 0
        let mut da = a;
        let mut i: usize = 0;
        while i < da.len()
            invariant
                0 <= i <= da.len(),
                da.len() == n,
                1 <= da.len() && da.len() <= 50000,
                forall|j: int| 0 <= j < i ==> da[j] == 0,
                forall|j: int| i <= j < da.len() as int ==> da[j] == a@[j],
            decreases da.len() - i,
        {
            da.set(i, 0);
            i += 1;
        }
        (n, da, b)
    } else if mutation_kind == 6 {
        // set all elements of b to 0
        let mut db = b;
        let mut i: usize = 0;
        while i < db.len()
            invariant
                0 <= i <= db.len(),
                db.len() == n,
                1 <= db.len() && db.len() <= 50000,
                forall|j: int| 0 <= j < i ==> db[j] == 0,
                forall|j: int| i <= j < db.len() as int ==> db[j] == b@[j],
            decreases db.len() - i,
        {
            db.set(i, 0);
            i += 1;
        }
        (n, a, db)
    } else if mutation_kind == 7 {
        // nudge first element of a up (if < 1000000000)
        let mut da = a;
        if da[0] < 1000000000 {
            da.set(0, da[0] + 1);
        }
        (n, da, b)
    } else if mutation_kind == 8 {
        // nudge first element of a down (if > 0)
        let mut da = a;
        if da[0] > 0 {
            da.set(0, da[0] - 1);
        }
        (n, da, b)
    } else if mutation_kind == 9 && a.len() >= 2 {
        // swap first two elements of a
        let mut da = a;
        let tmp = da[0];
        da.set(0, da[1]);
        da.set(1, tmp);
        (n, da, b)
    } else if mutation_kind == 10 && a.len() >= 2 {
        // swap first two elements of b
        let mut db = b;
        let tmp = db[0];
        db.set(0, db[1]);
        db.set(1, tmp);
        (n, a, db)
    } else if mutation_kind == 11 {
        // set a = b (always yields YES case with max_diff=0)
        let mut da = a;
        let mut i: usize = 0;
        while i < da.len()
            invariant
                0 <= i <= da.len(),
                da.len() == n,
                b.len() == n,
                1 <= da.len() && da.len() <= 50000,
                forall|j: int| 0 <= j < i ==> da[j] == b@[j],
                forall|j: int| i <= j < da.len() as int ==> da[j] == a@[j],
                forall|k: int| 0 <= k && k < b.len() ==> 0 <= b@[k] && b@[k] <= 1000000000,
            decreases da.len() - i,
        {
            da.set(i, b[i]);
            i += 1;
        }
        (n, da, b)
    } else {
        // fallback: identity
        (n, a, b)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(cases: &[(Vec<i32>, Vec<i32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        let p1: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&p1.join(" "));
        s.push('\n');
        let p2: Vec<String> = b.iter().map(|v| v.to_string()).collect();
        s.push_str(&p2.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn build_valid(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
    let k = rng.gen_range_i64(0, 50) as i32;
    let b: Vec<i32> = a.iter().map(|&x| if x >= k { x - k } else { 0 }).collect();
    (a, b)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[(Vec<i32>, Vec<i32>)], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<bool> = cases.iter().map(|(a, b)| Solution::is_possible(a.len(), a.clone(), b.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![3, 5, 4, 1], vec![1, 3, 2, 0]),
        (vec![1, 2, 1], vec![0, 1, 0]),
        (vec![5, 3, 7, 2], vec![1, 1, 1, 1]),
        (vec![1, 2, 3, 4, 5], vec![1, 2, 3, 4, 6]),
        (vec![1], vec![0]),
        (vec![8], vec![0]),
        (vec![14], vec![6]),
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<(Vec<i32>, Vec<i32>)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            let case = if rng.gen_range_i64(0, 1) == 0 {
                build_valid(&mut rng, n)
            } else {
                let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
                let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
                (a, b)
            };
            cases.push(case);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

