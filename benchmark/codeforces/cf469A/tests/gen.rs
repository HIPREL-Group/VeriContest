use vstd::prelude::*;

verus! {

fn unique_levels(raw: Vec<i32>, n: i32) -> (result: Vec<i32>)
    requires 1 <= n <= 100,
    ensures result.len() <= n,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= n,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > n as usize { n as usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= n, 1 <= n <= 100, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= n,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > n { n } else { v };
        let mut j = 0usize;
        let mut found = false;
        while j < result.len()
            invariant j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    result
}
pub fn generate_test_case(n: i32, x: Vec<i32>, y: Vec<i32>) -> (result: (i32, Vec<i32>, Vec<i32>))
    ensures 1 <= result.0 <= 100,
        result.1.len() <= result.0, result.2.len() <= result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= result.0,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall|i: int, j: int| 0 <= i < j < result.2.len() ==> result.2[i] != result.2[j],
{
    let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
    (n, unique_levels(x, n), unique_levels(y, n))
}


pub fn generate_candidate(
    n: i32,
    x_levels: Vec<i32>,
    y_levels: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100,
        forall|i: int| 0 <= i < x_levels.len() ==> 1 <= #[trigger] x_levels[i] && x_levels[i] <= n,
        forall|i: int| 0 <= i < y_levels.len() ==> 1 <= #[trigger] y_levels[i] && y_levels[i] <= n,
    ensures
        1 <= result.0 <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] && result.1[i] <= result.0,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] && result.2[i] <= result.0,
{
    if mutation_kind == 0 {
        // identity
        (n, x_levels, y_levels)
    } else if mutation_kind == 1 {
        // set all x_levels elements to 1
        let mut x = x_levels;
        let mut i: usize = 0;
        while i < x.len()
            invariant
                1 <= n <= 100,
                x.len() == x_levels.len(),
                0 <= i <= x.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] x[j] == 1,
                forall|j: int| i <= j < x.len() ==> 1 <= #[trigger] x[j] && x[j] <= n,
            decreases x.len() - i,
        {
            x.set(i, 1i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < x.len() implies 1 <= #[trigger] x[j] && x[j] <= n by {}
        (n, x, y_levels)
    } else if mutation_kind == 2 {
        // set all y_levels elements to 1
        let mut y = y_levels;
        let mut i: usize = 0;
        while i < y.len()
            invariant
                1 <= n <= 100,
                y.len() == y_levels.len(),
                0 <= i <= y.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] y[j] == 1,
                forall|j: int| i <= j < y.len() ==> 1 <= #[trigger] y[j] && y[j] <= n,
            decreases y.len() - i,
        {
            y.set(i, 1i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= #[trigger] y[j] && y[j] <= n by {}
        (n, x_levels, y)
    } else if mutation_kind == 3 {
        // set all x_levels elements to n
        let mut x = x_levels;
        let mut i: usize = 0;
        while i < x.len()
            invariant
                1 <= n <= 100,
                x.len() == x_levels.len(),
                0 <= i <= x.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] x[j] == n,
                forall|j: int| i <= j < x.len() ==> 1 <= #[trigger] x[j] && x[j] <= n,
            decreases x.len() - i,
        {
            x.set(i, n);
            i += 1;
        }
        assert forall|j: int| 0 <= j < x.len() implies 1 <= #[trigger] x[j] && x[j] <= n by {}
        (n, x, y_levels)
    } else if mutation_kind == 4 {
        // set all y_levels elements to n
        let mut y = y_levels;
        let mut i: usize = 0;
        while i < y.len()
            invariant
                1 <= n <= 100,
                y.len() == y_levels.len(),
                0 <= i <= y.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] y[j] == n,
                forall|j: int| i <= j < y.len() ==> 1 <= #[trigger] y[j] && y[j] <= n,
            decreases y.len() - i,
        {
            y.set(i, n);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 1 <= #[trigger] y[j] && y[j] <= n by {}
        (n, x_levels, y)
    } else if mutation_kind == 5 && x_levels.len() >= 1 {
        // set first x_levels element to 1
        let mut x = x_levels;
        x.set(0, 1i32);
        assert forall|j: int| 0 <= j < x.len() implies 1 <= #[trigger] x[j] && x[j] <= n by {}
        (n, x, y_levels)
    } else if mutation_kind == 6 && y_levels.len() >= 1 {
        // set first y_levels element to n
        let mut y = y_levels;
        y.set(0, n);
        assert forall|j: int| 0 <= j < y.len() implies 1 <= #[trigger] y[j] && y[j] <= n by {}
        (n, x_levels, y)
    } else if mutation_kind == 7 {
        // empty x_levels
        let x: Vec<i32> = Vec::new();
        (n, x, y_levels)
    } else if mutation_kind == 8 {
        // empty y_levels
        let y: Vec<i32> = Vec::new();
        (n, x_levels, y)
    } else if mutation_kind == 9 {
        // empty both
        let x: Vec<i32> = Vec::new();
        let y: Vec<i32> = Vec::new();
        (n, x, y)
    } else {
        // fallback: identity
        (n, x_levels, y_levels)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

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

fn build_input(n: i32, x: &[i32], y: &[i32]) -> String {
    let mut s = format!("{}\n", n);
    s.push_str(&format!("{}", x.len()));
    for &v in x { s.push_str(&format!(" {}", v)); }
    s.push('\n');
    s.push_str(&format!("{}", y.len()));
    for &v in y { s.push_str(&format!(" {}", v)); }
    s.push('\n');
    s
}

fn build_output(ans: bool) -> String {
    if ans {
        "I become the guy.\n".to_string()
    } else {
        "Oh, my keyboard!\n".to_string()
    }
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(469);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, x: Vec<i32>, y: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (n, x, y) = generate_test_case(n, x, y);
        if *count >= target_count { return; }
        let key = format!("{}_{:?}_{:?}", n, x, y);
        if !seen.insert(key) { return; }
        let result = Solution::can_be_the_guy(n, x.clone(), y.clone());
        let inp = build_input(n, &x, &y);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(4, vec![1, 2, 3], vec![2, 4], &mut seen, &mut out, &mut count);
    emit(4, vec![1, 2, 3], vec![2, 3], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(1, vec![1], vec![], &mut seen, &mut out, &mut count);
    emit(1, vec![], vec![1], &mut seen, &mut out, &mut count);
    emit(1, vec![], vec![], &mut seen, &mut out, &mut count);
    emit(2, vec![1, 2], vec![], &mut seen, &mut out, &mut count);
    emit(100, (1..=100).collect(), vec![], &mut seen, &mut out, &mut count);
    emit(100, vec![], (1..=100).collect(), &mut seen, &mut out, &mut count);
    emit(100, (1..=50).collect(), (51..=100).collect(), &mut seen, &mut out, &mut count);
    emit(100, (1..=50).collect(), (50..=99).collect(), &mut seen, &mut out, &mut count); // missing 100
    emit(50, (1..=50).collect(), (1..=50).collect(), &mut seen, &mut out, &mut count); // duplicate
    emit(10, vec![5], vec![5], &mut seen, &mut out, &mut count);

    // Random
    while count < target_count {
        let n = rng.gen_range_i64(1, 100) as i32;
        let p = rng.gen_range_usize(0, n as usize);
        let q = rng.gen_range_usize(0, n as usize);
        let mut x: Vec<i32> = Vec::new();
        for _ in 0..p {
            x.push(rng.gen_range_i64(1, n as i64) as i32);
        }
        let mut y: Vec<i32> = Vec::new();
        for _ in 0..q {
            y.push(rng.gen_range_i64(1, n as i64) as i32);
        }
        emit(n, x, y, &mut seen, &mut out, &mut count);
    }
}
