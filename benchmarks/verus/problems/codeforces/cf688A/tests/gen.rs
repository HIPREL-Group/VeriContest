use vstd::prelude::*;

verus! {

fn make_uniform_row(n: usize, val: u8) -> (row: Vec<u8>)
    requires
        1 <= n && n <= 100,
        val == 48u8 || val == 49u8,
    ensures
        row.len() == n,
        forall|j: int| 0 <= j && j < n ==> row@[j] == val,
{
    let mut row: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            row.len() == j,
            forall|k: int| 0 <= k && k < j ==> row@[k] == val,
        decreases n - j,
    {
        row.push(val);
        j = j + 1;
    }
    row
}

pub fn generate_test_case(
    n: usize,
    d: usize,
    days: Vec<Vec<u8>>,
    mutation_kind: u8,
) -> (result: (usize, usize, Vec<Vec<u8>>))
    requires
        1 <= n && n <= 100,
        1 <= d && d <= 100,
        days.len() == d,
        forall|i: int| 0 <= i && i < d ==> #[trigger] days@[i].len() == n,
        forall|i: int, j: int|
            0 <= i && i < d && 0 <= j && j < n
                ==> (#[trigger] days@[i]@[j] == 48u8 || #[trigger] days@[i]@[j] == 49u8),
    ensures
        1 <= result.0 && result.0 <= 100,
        1 <= result.1 && result.1 <= 100,
        result.2.len() == result.1,
        forall|i: int| 0 <= i && i < result.1 ==> #[trigger] result.2@[i].len() == result.0,
        forall|i: int, j: int|
            0 <= i && i < result.1 && 0 <= j && j < result.0
                ==> (#[trigger] result.2@[i]@[j] == 48u8 || #[trigger] result.2@[i]@[j] == 49u8),
{
    if mutation_kind == 0 {
        // identity
        (n, d, days)
    } else if mutation_kind == 1 {
        // set first row to all absent (48) — Arya wins that day
        let new_row = make_uniform_row(n, 48u8);
        let ghost old_days = days@;
        let mut days = days;
        days.set(0, new_row);
        proof {
            assert forall|i: int| 0 <= i && i < d
                implies #[trigger] days@[i].len() == n by {
                if i != 0 { assert(days@[i] =~= old_days[i]); }
            };
            assert forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                implies (#[trigger] days@[i]@[j] == 48u8
                    || #[trigger] days@[i]@[j] == 49u8) by {
                if i != 0 { assert(days@[i] =~= old_days[i]); }
            };
        }
        (n, d, days)
    } else if mutation_kind == 2 {
        // set first row to all present (49) — Arya loses that day
        let new_row = make_uniform_row(n, 49u8);
        let ghost old_days = days@;
        let mut days = days;
        days.set(0, new_row);
        proof {
            assert forall|i: int| 0 <= i && i < d
                implies #[trigger] days@[i].len() == n by {
                if i != 0 { assert(days@[i] =~= old_days[i]); }
            };
            assert forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                implies (#[trigger] days@[i]@[j] == 48u8
                    || #[trigger] days@[i]@[j] == 49u8) by {
                if i != 0 { assert(days@[i] =~= old_days[i]); }
            };
        }
        (n, d, days)
    } else if mutation_kind == 3 {
        // set last row to all absent (48)
        let new_row = make_uniform_row(n, 48u8);
        let ghost old_days = days@;
        let mut days = days;
        let last = d - 1;
        days.set(last, new_row);
        proof {
            assert forall|i: int| 0 <= i && i < d
                implies #[trigger] days@[i].len() == n by {
                if i != last as int { assert(days@[i] =~= old_days[i]); }
            };
            assert forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                implies (#[trigger] days@[i]@[j] == 48u8
                    || #[trigger] days@[i]@[j] == 49u8) by {
                if i != last as int { assert(days@[i] =~= old_days[i]); }
            };
        }
        (n, d, days)
    } else if mutation_kind == 4 {
        // set last row to all present (49)
        let new_row = make_uniform_row(n, 49u8);
        let ghost old_days = days@;
        let mut days = days;
        let last = d - 1;
        days.set(last, new_row);
        proof {
            assert forall|i: int| 0 <= i && i < d
                implies #[trigger] days@[i].len() == n by {
                if i != last as int { assert(days@[i] =~= old_days[i]); }
            };
            assert forall|i: int, j: int|
                0 <= i && i < d && 0 <= j && j < n
                implies (#[trigger] days@[i]@[j] == 48u8
                    || #[trigger] days@[i]@[j] == 49u8) by {
                if i != last as int { assert(days@[i] =~= old_days[i]); }
            };
        }
        (n, d, days)
    } else if mutation_kind == 5 {
        // construct all rows as all-absent (48) — Arya wins every day
        let mut days_new: Vec<Vec<u8>> = Vec::new();
        let mut i: usize = 0;
        while i < d
            invariant
                0 <= i <= d,
                1 <= n && n <= 100,
                1 <= d && d <= 100,
                days_new.len() == i,
                forall|k: int| 0 <= k && k < i
                    ==> #[trigger] days_new@[k].len() == n,
                forall|k: int, l: int|
                    0 <= k && k < i && 0 <= l && l < n
                    ==> (#[trigger] days_new@[k]@[l] == 48u8
                        || #[trigger] days_new@[k]@[l] == 49u8),
            decreases d - i,
        {
            let row = make_uniform_row(n, 48u8);
            days_new.push(row);
            i = i + 1;
        }
        (n, d, days_new)
    } else if mutation_kind == 6 {
        // construct all rows as all-present (49) — Arya loses every day
        let mut days_new: Vec<Vec<u8>> = Vec::new();
        let mut i: usize = 0;
        while i < d
            invariant
                0 <= i <= d,
                1 <= n && n <= 100,
                1 <= d && d <= 100,
                days_new.len() == i,
                forall|k: int| 0 <= k && k < i
                    ==> #[trigger] days_new@[k].len() == n,
                forall|k: int, l: int|
                    0 <= k && k < i && 0 <= l && l < n
                    ==> (#[trigger] days_new@[k]@[l] == 48u8
                        || #[trigger] days_new@[k]@[l] == 49u8),
            decreases d - i,
        {
            let row = make_uniform_row(n, 49u8);
            days_new.push(row);
            i = i + 1;
        }
        (n, d, days_new)
    } else {
        // fallback identity
        (n, d, days)
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
    let target: usize = 100;
    let mut rng = Rng::new(688);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit(2, vec![vec![b'1', b'0'], vec![b'0', b'0']], &mut seen, &mut out, &mut count);
    emit(4, vec![vec![b'0', b'1', b'0', b'0']], &mut seen, &mut out, &mut count);
    emit(4, vec![
        vec![b'1', b'1', b'0', b'1'],
        vec![b'1', b'1', b'1', b'1'],
        vec![b'0', b'1', b'1', b'0'],
        vec![b'1', b'0', b'1', b'1'],
        vec![b'1', b'1', b'1', b'1'],
    ], &mut seen, &mut out, &mut count);

    // Edges
    emit(1, vec![vec![b'0']], &mut seen, &mut out, &mut count);
    emit(1, vec![vec![b'1']], &mut seen, &mut out, &mut count);
    emit(1, vec![vec![b'1']; 100], &mut seen, &mut out, &mut count);
    emit(1, vec![vec![b'0']; 100], &mut seen, &mut out, &mut count);
    emit(100, vec![vec![b'1'; 100]], &mut seen, &mut out, &mut count);
    emit(100, vec![vec![b'0'; 100]], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 50);
        let d = rng.gen_range_usize(1, 50);
        let p = match rng.gen_range_usize(0, 4) {
            0 => 0.1,
            1 => 0.3,
            2 => 0.5,
            _ => 0.7,
        };
        let days = make_random_days(&mut rng, n, d, p);
        emit(n, days, &mut seen, &mut out, &mut count);
    }
}

