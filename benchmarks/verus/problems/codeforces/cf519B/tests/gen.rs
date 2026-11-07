use vstd::prelude::*;

verus! {

// Spec fn helpers from spec.rs

pub open spec fn all_errors_valid(s: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 1_000_000_000
}

pub open spec fn count_value(s: Seq<i64>, value: i64) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == value { 1int } else { 0int }) + count_value(s.subrange(1, s.len() as int), value)
    }
}

pub open spec fn single_deletion(from: Seq<i64>, to: Seq<i64>, deleted: i64) -> bool {
    from.len() == to.len() + 1
        && forall|v: i64| #[trigger] count_value(from, v) == count_value(to, v) + if v == deleted { 1int } else { 0int }
}

// Lemma: appending an element adds 1 to its count, 0 to all others
proof fn count_value_push_lemma(s: Seq<i64>, x: i64, v: i64)
    ensures
        count_value(s.push(x), v) == count_value(s, v) + (if x == v { 1int } else { 0int }),
    decreases s.len(),
{
    reveal_with_fuel(count_value, 3);
    if s.len() == 0 {
        assert(s.push(x).subrange(1, 1int) =~= Seq::<i64>::empty());
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(s.push(x).subrange(1, (s.len() + 1) as int) =~= tail.push(x));
        count_value_push_lemma(tail, x, v);
    }
}

pub fn generate_test_case(
    base: Vec<i64>,
    del_x: i64,
    del_y: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>, Vec<i64>))
    requires
        1 <= base.len() <= 99_998,
        all_errors_valid(base@),
        1 <= del_x <= 1_000_000_000,
        1 <= del_y <= 1_000_000_000,
    ensures
        3 <= result.0.len() <= 100_000,
        all_errors_valid(result.0@),
        all_errors_valid(result.1@),
        all_errors_valid(result.2@),
        exists|x: i64| single_deletion(result.0@, result.1@, x),
        exists|y: i64| single_deletion(result.1@, result.2@, y),
{
    // Mutation: swap deletion order for diversity
    let d1: i64 = if mutation_kind % 2 == 0 { del_y } else { del_x };
    let d2: i64 = if mutation_kind % 2 == 0 { del_x } else { del_y };

    let ghost base_view = base@;
    let n = base.len();

    // Build first = [base[0], ..., base[n-1], d1, d2]
    let mut first: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == base.len(),
            first.len() == i as int,
            base@ == base_view,
            forall|k: int| 0 <= k < i as int ==> #[trigger] first@[k] == base@[k],
            all_errors_valid(base@),
            1 <= n <= 99_998,
        decreases n - i,
    {
        first.push(base[i]);
        i = i + 1;
    }
    assert(first@ =~= base@);

    first.push(d1);
    first.push(d2);

    // Build second = [base[0], ..., base[n-1], d1]
    let mut second: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            n == base.len(),
            second.len() == j as int,
            base@ == base_view,
            forall|k: int| 0 <= k < j as int ==> #[trigger] second@[k] == base@[k],
            1 <= n <= 99_998,
        decreases n - j,
    {
        second.push(base[j]);
        j = j + 1;
    }
    assert(second@ =~= base@);

    second.push(d1);

    // Build third = copy of base
    let mut third: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == base.len(),
            third.len() == k as int,
            base@ == base_view,
            forall|kk: int| 0 <= kk < k as int ==> #[trigger] third@[kk] == base@[kk],
            1 <= n <= 99_998,
        decreases n - k,
    {
        third.push(base[k]);
        k = k + 1;
    }
    assert(third@ =~= base_view);

    proof {
        // Establish extensional equalities
        assert(first@ =~= second@.push(d2));
        assert(second@ =~= third@.push(d1));

        // Prove single_deletion(first@, second@, d2)
        assert forall|v: i64| #[trigger] count_value(first@, v) == count_value(second@, v) + if v == d2 { 1int } else { 0int }
        by {
            assert(first@ =~= second@.push(d2));
            count_value_push_lemma(second@, d2, v);
        };
        assert(single_deletion(first@, second@, d2));

        // Prove single_deletion(second@, third@, d1)
        assert forall|v: i64| #[trigger] count_value(second@, v) == count_value(third@, v) + if v == d1 { 1int } else { 0int }
        by {
            assert(second@ =~= third@.push(d1));
            count_value_push_lemma(third@, d1, v);
        };
        assert(single_deletion(second@, third@, d1));

        // Prove all_errors_valid for first
        assert(all_errors_valid(first@)) by {
            assert forall|idx: int| 0 <= idx < first@.len() implies 1 <= #[trigger] first@[idx] <= 1_000_000_000
            by {
                if idx < n as int {
                    assert(first@[idx] == base_view[idx]);
                } else if idx == n as int {
                    assert(first@[idx] == d1);
                } else {
                    assert(first@[idx] == d2);
                }
            };
        };

        // Prove all_errors_valid for second
        assert(all_errors_valid(second@)) by {
            assert forall|idx: int| 0 <= idx < second@.len() implies 1 <= #[trigger] second@[idx] <= 1_000_000_000
            by {
                if idx < n as int {
                    assert(second@[idx] == base_view[idx]);
                } else {
                    assert(second@[idx] == d1);
                }
            };
        };

        // Prove all_errors_valid for third (same as base)
        assert(all_errors_valid(third@)) by {
            assert forall|idx: int| 0 <= idx < third@.len() implies 1 <= #[trigger] third@[idx] <= 1_000_000_000
            by {
                assert(third@[idx] == base_view[idx]);
            };
        };

        // Explicitly provide witnesses for existential postconditions
        assert(exists|x: i64| single_deletion(first@, second@, x)) by {
            assert(single_deletion(first@, second@, d2));
        };
        assert(exists|y: i64| single_deletion(second@, third@, y)) by {
            assert(single_deletion(second@, third@, d1));
        };
    }

    let res = (first, second, third);
    proof {
        assert(single_deletion(res.0@, res.1@, d2));
        assert(single_deletion(res.1@, res.2@, d1));
    }
    res
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

// Build a valid (first, second, third) by picking two indices to remove.
fn make_test(rng: &mut Rng, n: usize) -> (Vec<i64>, Vec<i64>, Vec<i64>) {
    let first: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
    // Remove one element to form second
    let i_rm = rng.gen_range_usize(0, n - 1);
    let mut second = first.clone();
    second.remove(i_rm);
    // Permute second (optional)
    // Remove one from second to form third
    let j_rm = rng.gen_range_usize(0, n - 2);
    let mut third = second.clone();
    third.remove(j_rm);
    // Optionally shuffle to be more realistic
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
    let target_count: usize = 100;
    let mut rng = Rng::new(519);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Examples
    emit(vec![1, 5, 8, 123, 7], vec![123, 7, 5, 1], vec![5, 1, 7], &mut seen, &mut out, &mut count);
    emit(vec![1, 4, 3, 3, 5, 7], vec![3, 7, 5, 4, 3], vec![4, 3, 7, 5], &mut seen, &mut out, &mut count);

    // Edge: minimal n=3
    emit(vec![1, 2, 3], vec![2, 3], vec![3], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3], vec![1, 3], vec![3], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3], vec![1, 2], vec![1], &mut seen, &mut out, &mut count);

    // Duplicates
    emit(vec![5, 5, 5, 5], vec![5, 5, 5], vec![5, 5], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 2000),
        };
        let (f, s, t) = make_test(&mut rng, n);
        emit(f, s, t, &mut seen, &mut out, &mut count);
    }
}

