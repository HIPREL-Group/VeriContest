use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elems: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 200000,
        forall|j: int| 0 <= j < elems.len() as int ==> 1 <= #[trigger] elems[j] <= elems.len(),
    ensures
        1 <= result.len() <= 200000,
        forall|j: int| 0 <= j < result.len() as int ==> 1 <= #[trigger] result[j] <= result.len(),
{
    if mutation_kind == 0 {
        elems
    } else if mutation_kind == 1 && elems.len() < 200_000 {
        let ghost old_seq = elems@;
        let ghost old_len = elems.len();
        let mut d = elems;
        d.push(1);
        proof {
            assert(d@.len() == old_len + 1);
            assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
                if j < old_len as int {
                    assert(d[j] == old_seq[j]);
                    assert(1 <= old_seq[j] <= old_len as i32);
                    assert((old_len as i32) <= d.len() as i32);
                } else {
                    assert(d[j] == 1i32);
                }
            }
        }
        d
    } else if mutation_kind == 2 {
        let mut d = elems;
        d.set(0, 1);
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            if j == 0 {
                assert(d[0] == 1i32);
            }
        }
        d
    } else if mutation_kind == 3 {
        let mut d = elems;
        let n = d.len() as i32;
        d.set(0, n);
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            if j == 0 {
                assert(d[0] == n);
            }
        }
        d
    } else if mutation_kind == 4 {
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1);
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            if j == last as int {
                assert(d[last as int] == 1i32);
            }
        }
        d
    } else if mutation_kind == 5 {
        let mut d = elems;
        let last = d.len() - 1;
        let n = d.len() as i32;
        d.set(last, n);
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            if j == last as int {
                assert(d[last as int] == n);
            }
        }
        d
    } else if mutation_kind == 6 {
        let mut d = elems;
        let ghost old_len = d.len();
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len()
                    ==> 1 <= #[trigger] d[j] <= d.len(),
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 7 {
        let mut d = elems;
        let ghost old_len = d.len();
        let n = d.len() as i32;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == old_len,
                1 <= d.len() <= 200_000,
                n == d.len() as i32,
                forall|j: int| 0 <= j < i ==> d[j] == n,
                forall|j: int| i <= j < d.len()
                    ==> 1 <= #[trigger] d[j] <= d.len(),
            decreases d.len() - i,
        {
            d.set(i, n);
            i += 1;
        }
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            assert(d[j] == n);
        }
        d
    } else if mutation_kind == 8 && elems.len() >= 2 {
        let mut d = elems;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        assert forall|j: int| 0 <= j < d.len() as int implies 1 <= #[trigger] d[j] <= d.len() by {
            if j == 0 {
                assert(d[0] == last_val);
            } else if j == last as int {
                assert(d[last as int] == first_val);
            }
        }
        d
    } else {
        elems
    }
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // The example from description.md (single bundle)
    {
        let cases: Vec<Vec<i32>> = vec![
            vec![1, 1, 1, 2, 2, 3],
            vec![1, 2, 3, 4, 5],
            vec![5, 4, 3, 2, 1, 1],
            vec![1, 1, 1, 1, 1],
            vec![1],
        ];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_remaining_after_epic_transformation(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    let edges: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 2],
        vec![1, 1, 2, 2],
        vec![1, 1, 1, 2],
    ];
    for e in edges {
        if count >= target { break; }
        let cases: Vec<Vec<i32>> = vec![e];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_remaining_after_epic_transformation(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(2, 5),
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 100),
                _ => rng.gen_range_usize(100, 500),
            };
            let mut a: Vec<i32> = Vec::with_capacity(n);
            for _ in 0..n {
                a.push(rng.gen_range_i32(1, n as i32));
            }
            cases.push(a);
        }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_remaining_after_epic_transformation(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

