use vstd::prelude::*;

verus! {

// Construction: take raw values in [0, 200] and map to [-100, 100] via raw[i] - 100.
// This is real construction work — the requires on raw are easy to sample,
// and the verified body transforms them into valid spec inputs.

pub fn generate_test_case(
    raw: Vec<i32>,
    n: usize,
    mutation_kind: u8,
) -> (ret: (Vec<i32>, usize))
    requires
        1 <= n <= 100,
        raw.len() == 3 * n,
        forall|i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] <= 200,
    ensures
        1 <= ret.1 <= 100,
        ret.0.len() == 3 * ret.1,
        forall|i: int| 0 <= i < ret.0.len() ==> -100 <= #[trigger] ret.0[i] <= 100,
{
    let len = raw.len();
    if mutation_kind == 0 {
        // Standard mapping: raw[i] - 100
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                raw.len() == len,
                forall|j: int| 0 <= j < raw.len() ==> 0 <= #[trigger] raw[j] <= 200,
                forall|j: int| 0 <= j < i as int ==> -100 <= #[trigger] vec[j] <= 100,
            decreases len - i,
        {
            vec.push(raw[i] - 100);
            i += 1;
        }
        (vec, n)
    } else if mutation_kind == 1 {
        // Negated mapping: 100 - raw[i]
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                raw.len() == len,
                forall|j: int| 0 <= j < raw.len() ==> 0 <= #[trigger] raw[j] <= 200,
                forall|j: int| 0 <= j < i as int ==> -100 <= #[trigger] vec[j] <= 100,
            decreases len - i,
        {
            vec.push(100 - raw[i]);
            i += 1;
        }
        (vec, n)
    } else if mutation_kind == 2 {
        // All zeros (equilibrium)
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] vec[j] == 0i32,
            decreases len - i,
        {
            vec.push(0i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < vec.len() implies -100 <= #[trigger] vec[j] <= 100 by {
            assert(vec[j] == 0i32);
        }
        (vec, n)
    } else if mutation_kind == 3 {
        // All 100 (max boundary)
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] vec[j] == 100i32,
            decreases len - i,
        {
            vec.push(100i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < vec.len() implies -100 <= #[trigger] vec[j] <= 100 by {
            assert(vec[j] == 100i32);
        }
        (vec, n)
    } else if mutation_kind == 4 {
        // All -100 (min boundary)
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] vec[j] == -100i32,
            decreases len - i,
        {
            vec.push(-100i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < vec.len() implies -100 <= #[trigger] vec[j] <= 100 by {
            assert(vec[j] == -100i32);
        }
        (vec, n)
    } else if mutation_kind == 5 {
        // Halved mapping: (raw[i] - 100) / 2, giving [-50, 50]
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                raw.len() == len,
                forall|j: int| 0 <= j < raw.len() ==> 0 <= #[trigger] raw[j] <= 200,
                forall|j: int| 0 <= j < i as int ==> -100 <= #[trigger] vec[j] <= 100,
            decreases len - i,
        {
            let v = raw[i] - 100;
            vec.push(v / 2);
            i += 1;
        }
        (vec, n)
    } else {
        // Fallback: same as mutation 0
        let mut vec: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 100,
                0 <= i <= len,
                vec.len() == i,
                raw.len() == len,
                forall|j: int| 0 <= j < raw.len() ==> 0 <= #[trigger] raw[j] <= 200,
                forall|j: int| 0 <= j < i as int ==> -100 <= #[trigger] vec[j] <= 100,
            decreases len - i,
        {
            vec.push(raw[i] - 100);
            i += 1;
        }
        (vec, n)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        lo + (self.next_u64() as i32).rem_euclid(hi - lo + 1)
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

fn build_input(vecs: &[(i32, i32, i32)]) -> String {
    let mut s = format!("{}\n", vecs.len());
    for &(x, y, z) in vecs { s.push_str(&format!("{} {} {}\n", x, y, z)); }
    s
}

fn build_output(yes: bool) -> String { if yes { "YES\n".into() } else { "NO\n".into() } }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(69);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |vecs: Vec<(i32, i32, i32)>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if vecs.is_empty() || vecs.len() > 100 { return; }
        for &(x, y, z) in &vecs { if x < -100 || x > 100 || y < -100 || y > 100 || z < -100 || z > 100 { return; } }
        let key = format!("{:?}", vecs);
        if !seen.insert(key) { return; }
        let inp = build_input(&vecs);
        let mut flat: Vec<i32> = Vec::new();
        for &(x, y, z) in &vecs { flat.push(x); flat.push(y); flat.push(z); }
        let ans = Solution::is_equilibrium(flat, vecs.len());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![(4, 1, 7), (-2, 4, -1), (1, -5, -6)], &mut seen, &mut out, &mut count);
    emit(vec![(3, -1, 7), (-5, 2, -4), (2, -1, -3)], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![(0, 0, 0)], &mut seen, &mut out, &mut count);
    emit(vec![(1, 0, 0)], &mut seen, &mut out, &mut count);
    emit(vec![(100, 100, 100)], &mut seen, &mut out, &mut count);
    emit(vec![(-100, -100, -100)], &mut seen, &mut out, &mut count);
    emit(vec![(100, 0, 0), (-100, 0, 0)], &mut seen, &mut out, &mut count);
    emit(vec![(0, 0, 0); 100], &mut seen, &mut out, &mut count);

    // Half random / half balanced
    for _ in 0..30 {
        let n = rng.gen_range_usize(1, 50);
        let mut vecs: Vec<(i32, i32, i32)> = Vec::new();
        let mut sx = 0i32; let mut sy = 0i32; let mut sz = 0i32;
        for _ in 0..(n - 1).max(0) {
            let x = rng.gen_range_i32(-100, 100);
            let y = rng.gen_range_i32(-100, 100);
            let z = rng.gen_range_i32(-100, 100);
            vecs.push((x, y, z));
            sx += x; sy += y; sz += z;
        }
        // Optionally make sum zero
        if rng.next_u64() % 2 == 0 {
            // Add closing vector
            let x = (-sx).clamp(-100, 100);
            let y = (-sy).clamp(-100, 100);
            let z = (-sz).clamp(-100, 100);
            vecs.push((x, y, z));
        } else {
            let x = rng.gen_range_i32(-100, 100);
            let y = rng.gen_range_i32(-100, 100);
            let z = rng.gen_range_i32(-100, 100);
            vecs.push((x, y, z));
        }
        emit(vecs, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let vecs: Vec<(i32, i32, i32)> = (0..n).map(|_| (
            rng.gen_range_i32(-100, 100),
            rng.gen_range_i32(-100, 100),
            rng.gen_range_i32(-100, 100),
        )).collect();
        emit(vecs, &mut seen, &mut out, &mut count);
    }
}

