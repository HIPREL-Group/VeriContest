use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    cnt: Vec<i32>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 200_000,
        cnt.len() == 30,
        forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] cnt[i] <= n,
    ensures
        1 <= result.0 <= 200_000,
        result.1.len() == 30,
        forall|i: int| 0 <= i < 30 ==> 0 <= #[trigger] result.1[i] <= result.0,
{
    if mutation_kind == 0 {
        // identity
        (n, cnt)
    } else if mutation_kind == 1 {
        // set first cnt element to 0
        let mut c = cnt;
        c.set(0, 0);
        (n, c)
    } else if mutation_kind == 2 {
        // set first cnt element to n
        let mut c = cnt;
        c.set(0, n as i32);
        (n, c)
    } else if mutation_kind == 3 {
        // set last cnt element to 0
        let mut c = cnt;
        c.set(29, 0);
        (n, c)
    } else if mutation_kind == 4 {
        // set last cnt element to n
        let mut c = cnt;
        c.set(29, n as i32);
        (n, c)
    } else if mutation_kind == 5 {
        // increase n to 200_000 (cnt still valid since cnt[i] <= old n <= 200_000)
        (200_000usize, cnt)
    } else if mutation_kind == 6 && n < 200_000 {
        // nudge n up by 1
        (n + 1, cnt)
    } else if mutation_kind == 7 {
        // set all cnt to 0
        let mut c = cnt;
        let mut i: usize = 0;
        while i < 30
            invariant
                c.len() == 30,
                0 <= i <= 30,
                forall|j: int| 0 <= j < i as int ==> #[trigger] c@[j] == 0i32,
                forall|j: int| i as int <= j < 30 ==> #[trigger] c@[j] == cnt@[j],
            decreases 30 - i,
        {
            c.set(i, 0);
            i += 1;
        }
        (n, c)
    } else if mutation_kind == 8 {
        // set all cnt to n
        let n_i32 = n as i32;
        let mut c = cnt;
        let mut i: usize = 0;
        while i < 30
            invariant
                c.len() == 30,
                0 <= i <= 30,
                1 <= n <= 200_000,
                n_i32 == n as i32,
                forall|j: int| 0 <= j < i as int ==> #[trigger] c@[j] == n_i32,
                forall|j: int| i as int <= j < 30 ==> #[trigger] c@[j] == cnt@[j],
            decreases 30 - i,
        {
            c.set(i, n_i32);
            i += 1;
        }
        (n, c)
    } else if mutation_kind == 9 && n > 1 {
        // nudge n down by 1, clamp cnt
        let new_n = n - 1;
        let new_n_i32 = new_n as i32;
        let mut c = cnt;
        let mut i: usize = 0;
        while i < 30
            invariant
                c.len() == 30,
                0 <= i <= 30,
                1 <= new_n <= 199_999,
                new_n_i32 == new_n as i32,
                forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] c@[j] <= new_n_i32,
                forall|j: int| i as int <= j < 30 ==> #[trigger] c@[j] == cnt@[j],
                forall|k: int| 0 <= k < 30 ==> 0 <= #[trigger] cnt@[k] <= n as int,
            decreases 30 - i,
        {
            if c[i] > new_n_i32 {
                c.set(i, new_n_i32);
            }
            i += 1;
        }
        (new_n, c)
    } else if mutation_kind == 10 {
        // halve all cnt values
        let mut c = cnt;
        let mut i: usize = 0;
        while i < 30
            invariant
                c.len() == 30,
                0 <= i <= 30,
                1 <= n <= 200_000,
                forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] c@[j] <= n as int,
                forall|j: int| i as int <= j < 30 ==> #[trigger] c@[j] == cnt@[j],
                forall|k: int| 0 <= k < 30 ==> 0 <= #[trigger] cnt@[k] <= n as int,
            decreases 30 - i,
        {
            c.set(i, c[i] / 2);
            i += 1;
        }
        (n, c)
    } else {
        // fallback: identity
        (n, cnt)
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

fn count_bits(a: &[i32]) -> Vec<i32> {
    let mut cnt = vec![0i32; 30];
    for &x in a {
        for b in 0..30 {
            if ((x >> b) & 1) == 1 { cnt[b] += 1; }
        }
    }
    cnt
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for ks in answers {
        let parts: Vec<String> = ks.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_array(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i64(0, (1 << 30) - 1) as i32).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[Vec<i32>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|a| {
            let cnt = count_bits(a);
            Solution::valid_k_values(a.len(), cnt)
        }).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    let exs: Vec<Vec<i32>> = vec![
        vec![4, 4, 4, 4],
        vec![13, 7, 25, 19],
        vec![3, 5, 3, 1, 7, 1],
        vec![1],
        vec![0, 0, 0, 0, 0],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 100);
            let arr = random_array(&mut rng, n);
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

