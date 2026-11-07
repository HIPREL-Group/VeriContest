use vstd::prelude::*;

verus! {

pub open spec fn count_value(s: Seq<i64>, value: i64) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == value { 1int } else { 0int }) + count_value(s.subrange(1, s.len() as int), value)
    }
}

pub open spec fn all_errors_valid(s: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000
}

pub open spec fn single_deletion(from: Seq<i64>, to: Seq<i64>, deleted: i64) -> bool {
    from.len() == to.len() + 1
        && forall|v: i64| #[trigger] count_value(from, v) == count_value(to, v) + if v == deleted { 1int } else { 0int }
}

// Helper: count_value of a sequence constructed by filling with a constant
pub proof fn count_constant_seq(s: Seq<i64>, c: i64, v: i64)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == c,
    ensures
        count_value(s, v) == (if v == c { s.len() as int } else { 0int }),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies tail[i] == c by {
            assert(tail[i] == s[i + 1]);
        }
        count_constant_seq(tail, c, v);
    }
}

// Build a Vec<i64> of length n all equal to c
pub fn make_constant_vec(n: usize, c: i64) -> (v: Vec<i64>)
    ensures
        v.len() == n,
        forall|i: int| 0 <= i < v.len() ==> v[i] == c,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            forall|k: int| 0 <= k < v.len() ==> v[k] == c,
        decreases n - i,
    {
        v.push(c);
        i = i + 1;
    }
    v
}

// Generator: produces three sequences first, second, third where
// - first has length n (n >= 3) all equal to c
// - second has length n-1 all equal to c
// - third has length n-2 all equal to c
// This trivially satisfies the spec preconditions: single_deletion holds with deleted=c.
pub fn generate_test_case(n: usize, c: i64) -> (result: (Vec<i64>, Vec<i64>, Vec<i64>))
    requires
        3 <= n <= 100_000,
        1 <= c <= 1_000_000_000,
    ensures
        ({
            let (first, second, third) = result;
            &&& first.len() == n
            &&& second.len() == n - 1
            &&& third.len() == n - 2
            &&& 3 <= first.len() <= 100_000
            &&& all_errors_valid(first@)
            &&& all_errors_valid(second@)
            &&& all_errors_valid(third@)
            &&& exists|x: i64| single_deletion(first@, second@, x)
            &&& exists|y: i64| single_deletion(second@, third@, y)
        }),
{
    let first = make_constant_vec(n, c);
    let second = make_constant_vec(n - 1, c);
    let third = make_constant_vec(n - 2, c);

    proof {
        // Establish counts for first, second, third
        assert forall|v: i64| #[trigger] count_value(first@, v) == (if v == c { first@.len() as int } else { 0int }) by {
            count_constant_seq(first@, c, v);
        }
        assert forall|v: i64| #[trigger] count_value(second@, v) == (if v == c { second@.len() as int } else { 0int }) by {
            count_constant_seq(second@, c, v);
        }
        assert forall|v: i64| #[trigger] count_value(third@, v) == (if v == c { third@.len() as int } else { 0int }) by {
            count_constant_seq(third@, c, v);
        }

        assert(first@.len() == second@.len() + 1);
        assert(second@.len() == third@.len() + 1);

        assert forall|v: i64| #[trigger] count_value(first@, v) == count_value(second@, v) + (if v == c { 1int } else { 0int }) by {
            count_constant_seq(first@, c, v);
            count_constant_seq(second@, c, v);
        }
        assert(single_deletion(first@, second@, c));

        assert forall|v: i64| #[trigger] count_value(second@, v) == count_value(third@, v) + (if v == c { 1int } else { 0int }) by {
            count_constant_seq(second@, c, v);
            count_constant_seq(third@, c, v);
        }
        assert(single_deletion(second@, third@, c));

        assert(exists|x: i64| single_deletion(first@, second@, x)) by {
            assert(single_deletion(first@, second@, c));
        }
        assert(exists|y: i64| single_deletion(second@, third@, y)) by {
            assert(single_deletion(second@, third@, c));
        }
    }

    (first, second, third)
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

fn build_input(first: &[i64], second: &[i64], third: &[i64]) -> String {
    let n = first.len();
    let mut s = format!("{}\n", n);
    let p1: Vec<String> = first.iter().map(|x| x.to_string()).collect();
    s.push_str(&p1.join(" "));
    s.push('\n');
    let p2: Vec<String> = second.iter().map(|x| x.to_string()).collect();
    s.push_str(&p2.join(" "));
    s.push('\n');
    let p3: Vec<String> = third.iter().map(|x| x.to_string()).collect();
    s.push_str(&p3.join(" "));
    s.push('\n');
    s
}

fn make_test(rng: &mut Rng, n: usize, max_val: i64) -> (Vec<i64>, Vec<i64>, Vec<i64>) {
    let first: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_val)).collect();
    let i_rm = rng.gen_range_usize(0, n - 1);
    let mut second = first.clone();
    second.remove(i_rm);
    let j_rm = rng.gen_range_usize(0, n - 2);
    let mut third = second.clone();
    third.remove(j_rm);
    for k in (1..second.len()).rev() {
        let s = rng.gen_range_usize(0, k);
        second.swap(k, s);
    }
    for k in (1..third.len()).rev() {
        let s = rng.gen_range_usize(0, k);
        third.swap(k, s);
    }
    (first, second, third)
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(51904);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |first: Vec<i64>, second: Vec<i64>, third: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if first.len() < 3 { return; }
        if second.len() != first.len() - 1 { return; }
        if third.len() != first.len() - 2 { return; }
        let key = format!("{:?}_{:?}_{:?}", first, second, third);
        if !seen.insert(key) { return; }
        let result = Solution::find_compilation_errors(first.clone(), second.clone(), third.clone());
        let inp = build_input(&first, &second, &third);
        let outp = format!("{}\n{}\n", result.0, result.1);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n
    let (f1, s1, t1) = make_test(&mut rng, 100_000, 1_000_000_000);
    emit(f1, s1, t1, &mut seen, &mut out, &mut count);

    // All same value
    emit(vec![1; 100_000], vec![1; 99_999], vec![1; 99_998], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000; 100_000], vec![1_000_000_000; 99_999], vec![1_000_000_000; 99_998], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 6 {
            0 | 1 => rng.gen_range_usize(50_000, 100_000),
            2 => rng.gen_range_usize(10_000, 50_000),
            3 => rng.gen_range_usize(1000, 10_000),
            4 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(3, 100),
        };
        let (f, s, t) = make_test(&mut rng, n, 1_000_000_000);
        emit(f, s, t, &mut seen, &mut out, &mut count);
    }
}

