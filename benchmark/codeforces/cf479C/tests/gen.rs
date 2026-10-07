use vstd::prelude::*;

verus! {

// ---- spec fn helpers copied from spec.rs ----

pub open spec fn lex_ordered_pair(x: (i64, i64), y: (i64, i64)) -> bool {
    x.0 < y.0 || (x.0 == y.0 && x.1 <= y.1)
}

pub open spec fn ordered_exams(exams: Seq<(i64, i64)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < exams.len() ==> #[trigger] lex_ordered_pair(exams[i], exams[j])
}

// ---- delta sum helper (for proving a-value ordering) ----

pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

proof fn lemma_sum_deltas_nonneg(deltas: Seq<i64>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

// ---- generator ----

pub fn generate_test_case(
    deltas: &Vec<i64>,
    base_a: i64,
    gap: i64,
    mutation_kind: u8,
) -> (exams: Vec<(i64, i64)>)
    requires
        deltas.len() + 1 <= 5000,
        1 <= gap,
        gap + 1 <= base_a,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base_a as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        1 <= exams.len() <= 5000,
        ordered_exams(exams@),
        forall|i: int|
            0 <= i < exams.len() ==> 1 <= #[trigger] exams[i].1 < exams[i].0 <= 1_000_000_000,
{
    proof {
        lemma_sum_deltas_nonneg(deltas@, deltas.len() as int);
    }

    let n: usize = deltas.len() + 1;

    let actual_gap: i64 = if mutation_kind == 1 && gap > 1 {
        // Use gap = 1 (minimum gap mutation)
        1i64
    } else if mutation_kind == 2 && base_a - 1 > gap {
        // Use gap = base_a - 1 (maximum gap mutation, b=1 for first element)
        base_a - 1
    } else {
        gap
    };

    // Ensure actual_gap still satisfies constraints
    let final_gap: i64 = if actual_gap >= 1 && actual_gap + 1 <= base_a {
        actual_gap
    } else {
        gap
    };

    let mut exams: Vec<(i64, i64)> = Vec::new();
    let mut current_a: i64 = base_a;

    // Push first element
    exams.push((current_a, current_a - final_gap));

    proof {
        assert(exams[0] == (base_a, (base_a - final_gap) as i64));
        assert(exams[0].0 as int == base_a as int + sum_deltas(deltas@, 0));
    }

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            exams.len() == idx + 1,
            n == deltas.len() + 1,
            n <= 5000,
            1 <= final_gap,
            final_gap + 1 <= base_a,
            forall|k: int| 0 <= k < deltas.len() ==> 0 <= #[trigger] deltas[k],
            base_a as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            current_a as int == base_a as int + sum_deltas(deltas@, idx as int),
            forall|k: int| 0 <= k <= idx as int ==>
                (#[trigger] exams[k]).0 as int == base_a as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k <= idx as int ==>
                (#[trigger] exams[k]).1 as int == base_a as int + sum_deltas(deltas@, k) - final_gap as int,
            forall|k: int| 0 <= k < exams.len() ==>
                1 <= #[trigger] exams[k].1 < exams[k].0 <= 1_000_000_000,
            ordered_exams(exams@),
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let new_a: i64 = current_a + deltas[idx];

        proof {
            lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
            assert(new_a as int >= base_a as int);
            assert(base_a as int >= final_gap as int + 1);
        }

        let new_b: i64 = new_a - final_gap;

        proof {
            // new_a == base_a + sum_deltas(deltas, idx+1)
            assert(new_a as int == base_a as int + sum_deltas(deltas@, (idx + 1) as int));

            // Prove new_a <= 1_000_000_000
            assert(new_a as int <= 1_000_000_000int) by {
                lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
            };

            // Prove new_b >= 1
            assert(new_b >= 1int) by {
                lemma_sum_deltas_nonneg(deltas@, (idx + 1) as int);
                assert(new_a as int >= base_a as int);
                assert(base_a as int >= final_gap as int + 1);
            };

            // Prove lex ordering: new element vs all existing
            assert forall|k: int| 0 <= k < exams.len()
                implies #[trigger] lex_ordered_pair(exams[k], (new_a, new_b))
            by {
                // exams[k].0 == base_a + sum_deltas(deltas, k)
                // new_a == base_a + sum_deltas(deltas, idx+1)
                // k <= idx < idx+1, so sum_deltas(k) <= sum_deltas(idx+1)
                lemma_sum_deltas_mono(deltas@, k, (idx + 1) as int);
                if exams[k].0 < new_a {
                    // first disjunct of lex_ordered_pair
                } else {
                    // exams[k].0 == new_a, so sum_deltas(k) == sum_deltas(idx+1)
                    // same gap => exams[k].1 == new_b
                    assert(exams[k].1 as int == base_a as int + sum_deltas(deltas@, k) - final_gap as int);
                    assert(new_b as int == base_a as int + sum_deltas(deltas@, (idx + 1) as int) - final_gap as int);
                    assert(exams[k].1 <= new_b);
                }
            };
        }

        exams.push((new_a, new_b));

        proof {
            // Prove ordered_exams still holds
            assert forall|i2: int, j2: int| 0 <= i2 < j2 < exams.len()
                implies #[trigger] lex_ordered_pair(exams[i2], exams[j2])
            by {
                let new_idx = (exams.len() - 1) as int;
                if j2 < new_idx {
                    // both old
                } else {
                    // j2 == new_idx
                    assert(exams[j2] == (new_a, new_b));
                }
            };
        }

        current_a = new_a;
        idx = idx + 1;
    }

    exams
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

fn build_input(exams: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", exams.len());
    for (a, b) in exams {
        s.push_str(&format!("{} {}\n", a, b));
    }
    s
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(479);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |exams: Vec<(i64, i64)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if exams.is_empty() { return; }
        for (a, b) in &exams {
            if *b < 1 || *a <= *b || *a > 1_000_000_000 { return; }
        }
        let key = format!("{:?}", exams);
        if !seen.insert(key) { return; }
        // Sort like main.rs does
        let mut sorted = exams.clone();
        sorted.sort();
        let result = Solution::min_last_exam_day(sorted);
        let inp = build_input(&exams);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![(5, 2), (3, 1), (4, 2)], &mut seen, &mut out, &mut count);
    emit(vec![(6, 1), (5, 2), (4, 3)], &mut seen, &mut out, &mut count);

    // Edge
    emit(vec![(2, 1)], &mut seen, &mut out, &mut count);
    emit(vec![(1_000_000_000, 1)], &mut seen, &mut out, &mut count);
    emit(vec![(2, 1), (3, 2)], &mut seen, &mut out, &mut count);
    emit(vec![(2, 1), (3, 2), (4, 3), (5, 4)], &mut seen, &mut out, &mut count);
    emit(vec![(10, 1), (10, 2), (10, 3)], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(500, 3000),
        };
        let mut exams = Vec::with_capacity(n);
        for _ in 0..n {
            let a = rng.gen_range_i64(2, 1_000_000_000);
            let b = rng.gen_range_i64(1, a - 1);
            exams.push((a, b));
        }
        emit(exams, &mut seen, &mut out, &mut count);
    }
}

