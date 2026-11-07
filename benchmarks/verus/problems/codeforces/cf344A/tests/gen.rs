use vstd::prelude::*;

verus! {

pub open spec fn magnet_valid(seq: Seq<u8>, i: int) -> bool {
    0 <= i < seq.len() && (#[trigger] seq[i] as int == 0 || seq[i] as int == 1)
}

pub open spec fn magnets_valid(seq: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> magnet_valid(seq, i)
}

proof fn lemma_set_preserves_valid(old_seq: Seq<u8>, new_seq: Seq<u8>, idx: int, val: u8)
    requires
        magnets_valid(old_seq),
        0 <= idx < old_seq.len(),
        new_seq.len() == old_seq.len(),
        val == 0 || val == 1,
        new_seq[idx] == val,
        forall|k: int| 0 <= k < old_seq.len() && k != idx ==> new_seq[k] == old_seq[k],
    ensures
        magnets_valid(new_seq),
{
    assert forall|i: int| 0 <= i < new_seq.len() implies magnet_valid(new_seq, i) by {
        if i == idx {
            assert(new_seq[i] as int == val as int);
        } else {
            assert(new_seq[i] == old_seq[i]);
            assert(magnet_valid(old_seq, i));
        }
    }
}

pub fn generate_test_case(magnets: Vec<u8>, mutation_kind: u8) -> (result: Vec<u8>)
    requires
        1 <= magnets.len() <= 100000,
        magnets_valid(magnets@),
    ensures
        1 <= result.len() <= 100000,
        magnets_valid(result@),
{
    if mutation_kind == 0 {
        magnets
    } else if mutation_kind == 1 {
        let ghost old = magnets@;
        let mut r = magnets;
        let last = r.len() - 1;
        r.set(last, 0u8);
        proof { lemma_set_preserves_valid(old, r@, last as int, 0u8); }
        r
    } else if mutation_kind == 2 {
        let ghost old = magnets@;
        let mut r = magnets;
        let last = r.len() - 1;
        r.set(last, 1u8);
        proof { lemma_set_preserves_valid(old, r@, last as int, 1u8); }
        r
    } else if mutation_kind == 3 {
        let ghost old = magnets@;
        let mut r = magnets;
        r.set(0, 0u8);
        proof { lemma_set_preserves_valid(old, r@, 0int, 0u8); }
        r
    } else if mutation_kind == 4 {
        let ghost old = magnets@;
        let mut r = magnets;
        r.set(0, 1u8);
        proof { lemma_set_preserves_valid(old, r@, 0int, 1u8); }
        r
    } else if mutation_kind == 5 {
        let ghost old = magnets@;
        let mut r = magnets;
        let last = r.len() - 1;
        let val = if r[last] == 0u8 { 1u8 } else { 0u8 };
        r.set(last, val);
        proof { lemma_set_preserves_valid(old, r@, last as int, val); }
        r
    } else if mutation_kind == 6 && magnets.len() < 100000 {
        let mut r = magnets;
        r.push(0u8);
        assert forall|i: int| 0 <= i < r.len() implies magnet_valid(r@, i) by {
            if i < r.len() - 1 {
                assert(r@[i] == magnets@[i]);
                assert(magnet_valid(magnets@, i));
            } else {
                assert(r@[i] == 0u8);
            }
        }
        r
    } else if mutation_kind == 7 && magnets.len() < 100000 {
        let mut r = magnets;
        r.push(1u8);
        assert forall|i: int| 0 <= i < r.len() implies magnet_valid(r@, i) by {
            if i < r.len() - 1 {
                assert(r@[i] == magnets@[i]);
                assert(magnet_valid(magnets@, i));
            } else {
                assert(r@[i] == 1u8);
            }
        }
        r
    } else if mutation_kind == 8 && magnets.len() > 1 {
        let mut r = magnets;
        r.pop();
        assert forall|i: int| 0 <= i < r.len() implies magnet_valid(r@, i) by {
            assert(r@[i] == magnets@[i]);
            assert(magnet_valid(magnets@, i));
        }
        r
    } else if mutation_kind == 9 {
        let mut r = magnets;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == magnets.len(),
                1 <= r.len() <= 100000,
                forall|j: int| 0 <= j < i ==> r[j] == 0u8,
                forall|j: int| i <= j < r.len() ==> r[j] == magnets[j],
            decreases r.len() - i,
        {
            r.set(i, 0u8);
            i += 1;
        }
        assert forall|j: int| 0 <= j < r.len() implies magnet_valid(r@, j) by {
            assert(r[j] == 0u8);
        }
        r
    } else if mutation_kind == 10 {
        let mut r = magnets;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == magnets.len(),
                1 <= r.len() <= 100000,
                forall|j: int| 0 <= j < i ==> r[j] == 1u8,
                forall|j: int| i <= j < r.len() ==> r[j] == magnets[j],
            decreases r.len() - i,
        {
            r.set(i, 1u8);
            i += 1;
        }
        assert forall|j: int| 0 <= j < r.len() implies magnet_valid(r@, j) by {
            assert(r[j] == 1u8);
        }
        r
    } else if mutation_kind == 11 && magnets.len() >= 2 {
        let ghost old = magnets@;
        let mut r = magnets;
        let v0 = r[0];
        let v1 = r[1];
        proof {
            assert(magnet_valid(old, 0));
            assert(magnet_valid(old, 1));
        }
        r.set(0, v1);
        proof { lemma_set_preserves_valid(old, r@, 0int, v1); }
        let ghost mid = r@;
        r.set(1, v0);
        proof { lemma_set_preserves_valid(mid, r@, 1int, v0); }
        r
    } else {
        magnets
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

fn mutate(magnets: Vec<u8>, mk: u8) -> Vec<u8> {
    if mk == 0 {
        magnets
    } else if mk == 1 {
        let mut r = magnets; let last = r.len() - 1; r[last] = 0; r
    } else if mk == 2 {
        let mut r = magnets; let last = r.len() - 1; r[last] = 1; r
    } else if mk == 3 {
        let mut r = magnets; r[0] = 0; r
    } else if mk == 4 {
        let mut r = magnets; r[0] = 1; r
    } else if mk == 5 {
        let mut r = magnets; let last = r.len() - 1; r[last] = if r[last] == 0 { 1 } else { 0 }; r
    } else if mk == 6 && magnets.len() < 100000 {
        let mut r = magnets; r.push(0); r
    } else if mk == 7 && magnets.len() < 100000 {
        let mut r = magnets; r.push(1); r
    } else if mk == 8 && magnets.len() > 1 {
        let mut r = magnets; r.pop(); r
    } else if mk == 9 {
        let mut r = magnets; for i in 0..r.len() { r[i] = 0; } r
    } else if mk == 10 {
        let mut r = magnets; for i in 0..r.len() { r[i] = 1; } r
    } else if mk == 11 && magnets.len() >= 2 {
        let mut r = magnets; let v0 = r[0]; let v1 = r[1]; r[0] = v1; r[1] = v0; r
    } else {
        magnets
    }
}

fn random_magnets(rng: &mut Rng, len: usize) -> Vec<u8> {
    (0..len).map(|_| (rng.next_u64() % 2) as u8).collect()
}

fn build_input(magnets: &[u8]) -> String {
    let mut s = format!("{}\n", magnets.len());
    for &m in magnets {
        if m == 0 { s.push_str("01\n"); } else { s.push_str("10\n"); }
    }
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

    let mut emit = |magnets: Vec<u8>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if magnets.is_empty() || magnets.len() > 100000 { return; }
        let key = format!("{:?}", magnets);
        if !seen.insert(key) { return; }
        let inp = build_input(&magnets);
        let ans = Solution::count_magnet_groups(magnets.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: Vec<Vec<u8>> = vec![
        vec![1, 1, 1, 0, 1, 1],
        vec![0, 0, 1, 1],
    ];
    for ex in &examples {
        for mk in 0..=11u8 {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    let seeds: Vec<Vec<u8>> = vec![
        vec![0], vec![1], vec![0, 0], vec![1, 1], vec![0, 1], vec![1, 0],
        vec![0, 1, 0, 1, 0], vec![1, 0, 1, 0, 1],
        vec![0, 0, 0, 0, 0], vec![1, 1, 1, 1, 1],
        vec![0, 0, 1, 1, 0, 0],
        vec![0, 0, 0, 1, 1, 1, 0, 0, 0],
    ];
    for seed in &seeds {
        for mk in 0..=11u8 {
            emit(mutate(seed.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let len = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let magnets = random_magnets(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(magnets, mk), &mut seen, &mut out, &mut count);
    }
}

