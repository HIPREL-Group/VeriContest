use vstd::prelude::*;

verus! {

pub open spec fn final_position(s: Seq<u8>, t: Seq<u8>, k: int) -> int
    recommends
        0 <= k <= t.len(),
        s.len() >= 1,
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        let prev = final_position(s, t, k - 1);
        if 0 <= prev && prev < s.len() && s[prev] == t[k - 1] {
            prev + 1
        } else {
            prev
        }
    }
}

proof fn lemma_final_position_bounds(s: Seq<u8>, t: Seq<u8>, k: int)
    requires
        0 <= k <= t.len(),
    ensures
        0 <= final_position(s, t, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_final_position_bounds(s, t, k - 1);
    }
}

pub fn generate_test_case(
    raw_s: Vec<u8>,
    raw_t: Vec<u8>,
    mutation_kind: u8,
) -> (result: (Vec<u8>, Vec<u8>))
    requires
        2 <= raw_s.len() <= 50,
        1 <= raw_t.len() <= 50,
        raw_t.len() < raw_s.len(),
        forall|i: int| 0 <= i < raw_s.len() ==> #[trigger] raw_s[i] <= 2u8,
        forall|i: int| 0 <= i < raw_t.len() ==> #[trigger] raw_t[i] <= 2u8,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1.len() <= 50,
        result.1.len() < result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 2u8,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 2u8,
        final_position(result.0@, result.1@, result.1.len() as int) < result.0.len(),
{
    proof {
        lemma_final_position_bounds(raw_s@, raw_t@, raw_t.len() as int);
    }
    let n_s = raw_s.len();
    let n_t = raw_t.len();
    if mutation_kind == 0 {
        (raw_s, raw_t)
    } else if mutation_kind == 1 {
        let mut s = raw_s;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == n_s,
                2 <= n_s <= 50,
                forall|j: int| 0 <= j < i ==> s[j] == 0u8,
                forall|j: int| i <= j < s.len() ==> #[trigger] s[j] <= 2u8,
            decreases s.len() - i,
        {
            s.set(i, 0u8);
            i += 1;
        }
        proof {
            lemma_final_position_bounds(s@, raw_t@, raw_t.len() as int);
        }
        (s, raw_t)
    } else if mutation_kind == 2 {
        let mut t = raw_t;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == n_t,
                1 <= n_t <= 50,
                forall|j: int| 0 <= j < i ==> t[j] == 2u8,
                forall|j: int| i <= j < t.len() ==> #[trigger] t[j] <= 2u8,
            decreases t.len() - i,
        {
            t.set(i, 2u8);
            i += 1;
        }
        proof {
            lemma_final_position_bounds(raw_s@, t@, t.len() as int);
        }
        (raw_s, t)
    } else {
        (raw_s, raw_t)
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

fn build_input(s_str: &str, t_str: &str) -> String {
    format!("{}\n{}\n", s_str, t_str)
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn map_color(b: u8) -> u8 {
    match b {
        b'R' => 0u8, b'G' => 1u8, b'B' => 2u8, _ => 0u8,
    }
}

fn rand_str(rng: &mut Rng, n: usize) -> String {
    let chars = ['R', 'G', 'B'];
    (0..n).map(|_| chars[(rng.next_u64() as usize) % 3]).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(265);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |s_str: &str, t_str: &str, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if s_str.is_empty() || t_str.is_empty() { return false; }
        if s_str.len() > 50 || t_str.len() > 50 { return false; }
        let inp = build_input(s_str, t_str);
        if !seen.insert(inp.clone()) { return false; }
        let s_v: Vec<u8> = s_str.bytes().map(map_color).collect();
        let t_v: Vec<u8> = t_str.bytes().map(map_color).collect();
        // Simulate to validate precondition (final_pos within bounds)
        let mut pos: usize = 0;
        let mut idx = 0;
        let mut ok = true;
        while idx < t_v.len() {
            if pos < s_v.len() && s_v[pos] == t_v[idx] {
                pos += 1;
            }
            if pos >= s_v.len() { ok = false; break; }
            idx += 1;
        }
        if !ok { return false; }
        let ans = Solution::final_pos(s_v, t_v);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
        true
    };

    // Sample tests
    emit("RGB", "RRR", &mut seen, &mut out, &mut count);
    emit("RRRBGBRBBB", "BBBRR", &mut seen, &mut out, &mut count);
    emit("BRRBGBRGRBGRGRRGGBGBGBRGBRGRGGGRBRRRBRBBBGRRRGGBBB", "BBRBGGRGRGBBBRBGRBRBBBBRBRRRBGBBGBBRRBBGGRBRRBRGRB", &mut seen, &mut out, &mut count);

    // Random tests
    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_usize(2, 50);
        let m = rng.gen_range_usize(1, n.saturating_sub(1).max(1));
        let m = m.min(n.saturating_sub(1)).max(1);
        let s = rand_str(&mut rng, n);
        let t = rand_str(&mut rng, m);
        emit(&s, &t, &mut seen, &mut out, &mut count);
    }
}
