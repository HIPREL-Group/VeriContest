use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    d: usize,
    bits: &Vec<Vec<u8>>,
) -> (result: (usize, usize, Vec<Vec<u8>>))
    requires
        1 <= n <= 100,
        1 <= d <= 100,
        bits.len() == d,
        forall|i: int| 0 <= i < d as int ==> #[trigger] bits@[i].len() == n,
        forall|i: int, j: int| 0 <= i < d as int && 0 <= j < n as int
            ==> (#[trigger] bits@[i]@[j] == 48u8 || bits@[i]@[j] == 49u8),
    ensures
        result.0 == n,
        result.1 == d,
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        result.2.len() == d,
        forall|i: int| 0 <= i < d as int ==> #[trigger] result.2@[i].len() == n,
        forall|i: int, j: int| 0 <= i < d as int && 0 <= j < n as int
            ==> (#[trigger] result.2@[i]@[j] == 48u8 || result.2@[i]@[j] == 49u8),
{
    let mut days: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < d
        invariant
            1 <= n <= 100,
            1 <= d <= 100,
            i <= d,
            days.len() == i,
            bits.len() == d,
            forall|k: int| 0 <= k < d as int ==> #[trigger] bits@[k].len() == n,
            forall|k: int, j: int| 0 <= k < d as int && 0 <= j < n as int
                ==> (#[trigger] bits@[k]@[j] == 48u8 || bits@[k]@[j] == 49u8),
            forall|k: int| 0 <= k < i as int ==> #[trigger] days@[k].len() == n,
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < n as int
                ==> (#[trigger] days@[k]@[j] == 48u8 || days@[k]@[j] == 49u8),
        decreases d - i,
    {
        let mut row: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                n <= 100,
                row.len() == j,
                i < d,
                bits.len() == d,
                bits@[i as int].len() == n,
                forall|jj: int| 0 <= jj < n as int
                    ==> (#[trigger] bits@[i as int]@[jj] == 48u8 || bits@[i as int]@[jj] == 49u8),
                forall|jj: int| 0 <= jj < j as int
                    ==> (#[trigger] row@[jj] == 48u8 || row@[jj] == 49u8),
            decreases n - j,
        {
            let b = bits[i][j];
            let v: u8 = if b == 49u8 { 49u8 } else { 48u8 };
            row.push(v);
            j = j + 1;
        }
        assert(row.len() == n);
        days.push(row);
        i = i + 1;
    }
    (n, d, days)
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

fn build_input(n: usize, days: &[Vec<u8>]) -> String {
    let mut s = format!("{} {}\n", n, days.len());
    for row in days {
        s.push_str(std::str::from_utf8(row).unwrap());
        s.push('\n');
    }
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn make_random_days(rng: &mut Rng, n: usize, d: usize, p_absent: f64) -> Vec<Vec<u8>> {
    let mut days = Vec::with_capacity(d);
    for _ in 0..d {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            let r = (rng.next_u64() % 1_000_000) as f64 / 1_000_000.0;
            row.push(if r < p_absent { b'0' } else { b'1' });
        }
        days.push(row);
    }
    days
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(68801);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, days: Vec<Vec<u8>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 100 || days.is_empty() || days.len() > 100 { return; }
        for r in &days { if r.len() != n { return; } for &c in r { if c != b'0' && c != b'1' { return; } } }
        let key = format!("{}|{:?}", n, days);
        if !seen.insert(key) { return; }
        let inp = build_input(n, &days);
        let ans = Solution::max_consecutive_winning_days(n, days.len(), &days);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    for &n in &[1usize, 2, 50, 99, 100] {
        for &d in &[1usize, 2, 50, 99, 100] {
            emit(n, vec![vec![b'1'; n]; d], &mut seen, &mut out, &mut count);
            emit(n, vec![vec![b'0'; n]; d], &mut seen, &mut out, &mut count);
            // alternate
            let alt: Vec<Vec<u8>> = (0..d).map(|i| if i % 2 == 0 { vec![b'1'; n] } else { vec![b'0'; n] }).collect();
            emit(n, alt, &mut seen, &mut out, &mut count);
        }
    }

    // single absent at varying positions
    for n in 1..=10usize {
        for d in 1..=10usize {
            let mut rows: Vec<Vec<u8>> = vec![vec![b'1'; n]; d];
            if !rows.is_empty() && n > 0 { rows[0][0] = b'0'; }
            emit(n, rows, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let d = rng.gen_range_usize(1, 100);
        let p = match rng.gen_range_usize(0, 5) {
            0 => 0.05,
            1 => 0.2,
            2 => 0.5,
            3 => 0.8,
            _ => 0.95,
        };
        let days = make_random_days(&mut rng, n, d, p);
        emit(n, days, &mut seen, &mut out, &mut count);
    }
}

