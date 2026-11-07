use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    coords: &Vec<i64>,
    heights: &Vec<i64>,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        coords.len() == heights.len(),
        1 <= coords.len() <= 100_000,
        forall |j: int| 0 <= j < coords.len() ==> 1 <= #[trigger] coords[j] <= 1_000_000_000,
        forall |j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 1_000_000_000,
        forall |j: int| 0 <= j < coords.len() - 1 ==> coords[j] < #[trigger] coords[j + 1],
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall |j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0@[j] <= 1_000_000_000,
        forall |j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1@[j] <= 1_000_000_000,
        forall |j: int| 0 <= j < result.0.len() - 1 ==> result.0@[j] < #[trigger] result.0@[j + 1],
{
    let n = coords.len();
    let mut x: Vec<i64> = Vec::new();
    let mut h: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == coords.len(),
            n == heights.len(),
            i <= n,
            x.len() == i,
            h.len() == i,
            forall |j: int| 0 <= j < coords.len() ==> 1 <= #[trigger] coords[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < heights.len() ==> 1 <= #[trigger] heights[j] <= 1_000_000_000,
            forall |j: int| 0 <= j < coords.len() - 1 ==> coords[j] < #[trigger] coords[j + 1],
            forall |j: int| 0 <= j < i ==> x@[j] == coords[j],
            forall |j: int| 0 <= j < i ==> h@[j] == heights[j],
        decreases n - i,
    {
        x.push(coords[i]);
        h.push(heights[i]);
        i = i + 1;
    }

    assert(x.len() == n);
    assert(h.len() == n);
    assert forall |j: int| 0 <= j < x.len() implies 1 <= #[trigger] x@[j] <= 1_000_000_000 by {
        assert(x@[j] == coords[j]);
    }
    assert forall |j: int| 0 <= j < h.len() implies 1 <= #[trigger] h@[j] <= 1_000_000_000 by {
        assert(h@[j] == heights[j]);
    }
    assert forall |j: int| 0 <= j < x.len() - 1 implies x@[j] < #[trigger] x@[j + 1] by {
        assert(x@[j] == coords[j]);
        assert(x@[j + 1] == coords[j + 1]);
    }

    (x, h)
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

fn build_input(x: &[i64], h: &[i64]) -> String {
    let n = x.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", x[i], h[i]));
    }
    s
}

fn random_trees(rng: &mut Rng, n: usize, max_x: i64) -> (Vec<i64>, Vec<i64>) {
    let mut xs: HashSet<i64> = HashSet::new();
    let mut tries = 0;
    while xs.len() < n {
        if tries > n * 20 { break; }
        xs.insert(rng.gen_range_i64(1, max_x));
        tries += 1;
    }
    if xs.len() < n {
        // fallback: dense
        xs.clear();
        for i in 1..=n as i64 {
            xs.insert(i);
        }
    }
    let mut x: Vec<i64> = xs.into_iter().collect();
    x.sort();
    let h: Vec<i64> = (0..x.len()).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
    (x, h)
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(54505);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |x: Vec<i64>, h: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if x.is_empty() || x.len() != h.len() { return; }
        for i in 1..x.len() {
            if x[i] <= x[i-1] { return; }
        }
        for &xi in &x { if xi < 1 || xi > 1_000_000_000 { return; } }
        for &hi in &h { if hi < 1 || hi > 1_000_000_000 { return; } }
        let key = format!("{:?}_{:?}", x, h);
        if !seen.insert(key) { return; }
        let result = Solution::max_felled_trees(x.clone(), h.clone());
        let inp = build_input(&x, &h);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: dense trees with large heights
    let n_max = 100_000;
    let dense_x: Vec<i64> = (1..=n_max as i64).collect();
    let dense_h: Vec<i64> = vec![1_000_000_000; n_max];
    emit(dense_x.clone(), dense_h.clone(), &mut seen, &mut out, &mut count);

    let dense_x2: Vec<i64> = (0..n_max as i64).map(|i| i * 2 + 1).collect();
    emit(dense_x2.clone(), dense_h.clone(), &mut seen, &mut out, &mut count);

    let small_h: Vec<i64> = vec![1; n_max];
    emit(dense_x.clone(), small_h, &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 | 1 => rng.gen_range_usize(50_000, 100_000),
            2 => rng.gen_range_usize(10_000, 50_000),
            3 => rng.gen_range_usize(1000, 10_000),
            _ => rng.gen_range_usize(100, 1000),
        };
        let max_x = (n as i64 * 4).max(1_000_000_000.min((n as i64 + 1) * 1_000_000_000 / (n as i64).max(1)));
        let max_x = max_x.min(1_000_000_000).max(n as i64);
        let (x, h) = random_trees(&mut rng, n, max_x);
        emit(x, h, &mut seen, &mut out, &mut count);
    }
}

