use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, targets: Vec<i64>, mutation_kind: u8) -> (result: (i64, Vec<i64>))
    requires
        1 <= n as int <= 100_000,
        targets.len() as int <= 100_000,
        forall|i: int| 0 <= i < targets.len() ==> 1 <= #[trigger] targets[i] as int <= n as int,
    ensures
        1 <= result.0 as int <= 100_000,
        result.1.len() as int <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] as int <= result.0 as int,
{
    if mutation_kind == 0 {
        // identity
        (n, targets)
    } else if mutation_kind == 1 {
        // set all targets to 1
        let mut y = targets;
        let len = y.len();
        let mut j: usize = 0;
        while j < len
            invariant
                len == y.len(),
                len as int <= 100_000,
                0 <= j <= len,
                1 <= n as int <= 100_000,
                forall|k: int| 0 <= k < j ==> (#[trigger] y[k] == 1i64),
                forall|k: int| j <= k < len as int ==> 1 <= (#[trigger] y[k] as int) <= n as int,
            decreases len - j,
        {
            y.set(j, 1i64);
            j += 1;
        }
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 2 {
        // set all targets to n
        let mut y = targets;
        let len = y.len();
        let mut j: usize = 0;
        while j < len
            invariant
                len == y.len(),
                len as int <= 100_000,
                0 <= j <= len,
                1 <= n as int <= 100_000,
                forall|k: int| 0 <= k < j ==> (#[trigger] y[k] == n),
                forall|k: int| j <= k < len as int ==> 1 <= (#[trigger] y[k] as int) <= n as int,
            decreases len - j,
        {
            y.set(j, n);
            j += 1;
        }
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 3 && targets.len() >= 1 {
        // set first target to 1
        let mut y = targets;
        y.set(0, 1i64);
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 4 && targets.len() >= 1 {
        // set first target to n (max distance from start=1 if n>1)
        let mut y = targets;
        y.set(0, n);
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 5 && targets.len() >= 1 {
        // set last target to 1
        let mut y = targets;
        let last = y.len() - 1;
        y.set(last, 1i64);
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 6 && targets.len() >= 1 {
        // set last target to n
        let mut y = targets;
        let last = y.len() - 1;
        y.set(last, n);
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else if mutation_kind == 7 && targets.len() >= 2 {
        // swap first two targets
        let mut y = targets;
        let a = y[0];
        let b = y[1];
        y.set(0, b);
        y.set(1, a);
        assert forall|k: int| 0 <= k < y.len() implies 1 <= (#[trigger] y[k] as int) <= n as int by {}
        (n, y)
    } else {
        // fallback: identity
        (n, targets)
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

fn mutate(n: i64, targets: Vec<i64>, mk: u8) -> (i64, Vec<i64>) {
    if mk == 0 {
        (n, targets)
    } else if mk == 1 {
        let mut y = targets;
        for j in 0..y.len() { y[j] = 1; }
        (n, y)
    } else if mk == 2 {
        let mut y = targets;
        for j in 0..y.len() { y[j] = n; }
        (n, y)
    } else if mk == 3 && targets.len() >= 1 {
        let mut y = targets; y[0] = 1; (n, y)
    } else if mk == 4 && targets.len() >= 1 {
        let mut y = targets; y[0] = n; (n, y)
    } else if mk == 5 && targets.len() >= 1 {
        let mut y = targets; let last = y.len() - 1; y[last] = 1; (n, y)
    } else if mk == 6 && targets.len() >= 1 {
        let mut y = targets; let last = y.len() - 1; y[last] = n; (n, y)
    } else if mk == 7 && targets.len() >= 2 {
        let mut y = targets;
        let a = y[0]; let b = y[1]; y[0] = b; y[1] = a;
        (n, y)
    } else {
        (n, targets)
    }
}

fn random_targets(rng: &mut Rng, m: usize, n: i64) -> Vec<i64> {
    (0..m).map(|_| rng.gen_range_i64(1, n)).collect()
}

fn build_input(n: i64, targets: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, targets.len());
    let parts: Vec<String> = targets.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i64, targets: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(2 <= n && n <= 100_000) { return; }
        if targets.is_empty() || targets.len() > 100_000 { return; }
        for &t in &targets {
            if !(1 <= t && t <= n) { return; }
        }
        let key = format!("{} {:?}", n, targets);
        if !seen.insert(key) { return; }
        let inp = build_input(n, &targets);
        let ans = Solution::total_steps(n, targets.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(4, vec![3, 2, 3], &mut seen, &mut out, &mut count);
    emit(4, vec![2, 3, 3], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 6 {
            0 => 2,
            1 => rng.gen_range_i64(2, 10),
            2 => rng.gen_range_i64(10, 100),
            3 => rng.gen_range_i64(100, 1000),
            4 => rng.gen_range_i64(1000, 10000),
            _ => rng.gen_range_i64(10000, 100_000),
        };
        let m = match tries % 5 {
            0 => 1,
            1 => 1,
            2 => rng.gen_range_usize(2, 10),
            3 => rng.gen_range_usize(10, 1000),
            _ => rng.gen_range_usize(1000, 100_000),
        };
        let targets = random_targets(&mut rng, m, n);
        let mk = (rng.next_u64() % 9) as u8;
        let (n_out, t_out) = mutate(n, targets, mk);
        emit(n_out, t_out, &mut seen, &mut out, &mut count);
    }
}

