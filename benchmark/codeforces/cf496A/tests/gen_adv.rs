use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    gaps: &Vec<i32>,
) -> (a: Vec<i32>)
    requires
        1 <= start as int,
        gaps.len() >= 2,
        gaps.len() <= 99,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i],
        // Bound cumulative sum: start + sum of gaps <= 1000
        start as int + (gaps.len() as int) * 10 <= 1000,
        forall|i: int| 0 <= i < gaps.len() ==> #[trigger] gaps[i] <= 10,
    ensures
        a.len() >= 3,
        a.len() <= 100,
        a.len() == gaps.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a@[i] <= 1000,
        forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a@[i] < a@[i + 1],
{
    let mut a: Vec<i32> = Vec::new();
    a.push(start);
    assert(a.len() == 1);
    assert(a@[0] == start);

    let mut cur: i32 = start;
    let mut idx: usize = 0;
    let n: usize = gaps.len();

    while idx < n
        invariant
            n == gaps.len(),
            0 <= idx <= n,
            a.len() == idx + 1,
            1 <= cur as int <= 1000,
            a@[a.len() - 1] == cur,
            cur as int <= start as int + (idx as int) * 10,
            start as int + (n as int) * 10 <= 1000,
            1 <= start as int,
            forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 10,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a@[k] <= 1000,
            forall|k: int| 0 <= k < a.len() - 1 ==> #[trigger] a@[k] < a@[k + 1],
        decreases n - idx,
    {
        let g = gaps[idx];
        assert(1 <= g as int <= 10);
        let new_cur: i32 = cur + g;
        assert(new_cur as int == cur as int + g as int);
        assert(new_cur as int <= start as int + (idx as int + 1) * 10);
        assert(new_cur as int <= 1000);
        assert(new_cur as int >= 2);
        a.push(new_cur);
        assert(a@[a.len() - 2] == cur);
        assert(a@[a.len() - 1] == new_cur);
        cur = new_cur;
        idx = idx + 1;
    }

    a
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn random_increasing_distinct(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut set: HashSet<i32> = HashSet::new();
    while set.len() < n {
        set.insert(rng.gen_range_i64(1, 1000) as i32);
    }
    let mut v: Vec<i32> = set.into_iter().collect();
    v.sort();
    v
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(49603);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if a.len() < 3 || a.len() > 100 { return; }
        for i in 1..a.len() {
            if a[i] <= a[i-1] { return; }
        }
        if a[0] < 1 || a[a.len()-1] > 1000 { return; }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let result = Solution::min_max_difficulty(a.clone());
        let inp = build_input(&a);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n
    emit((1..=100).collect(), &mut seen, &mut out, &mut count);
    emit((901..=1000).collect(), &mut seen, &mut out, &mut count);
    let mut spaced: Vec<i32> = (1..=100).map(|i| i * 10).collect();
    spaced[0] = 1;
    emit(spaced, &mut seen, &mut out, &mut count);

    // Two big gaps
    emit(vec![1, 100, 200, 1000], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 500, 1000], &mut seen, &mut out, &mut count);
    emit(vec![1, 500, 999, 1000], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 4 {
            0 | 1 => rng.gen_range_usize(50, 100),
            2 => rng.gen_range_usize(20, 80),
            _ => rng.gen_range_usize(3, 30),
        };
        let a = random_increasing_distinct(&mut rng, n);
        emit(a, &mut seen, &mut out, &mut count);
    }
}

