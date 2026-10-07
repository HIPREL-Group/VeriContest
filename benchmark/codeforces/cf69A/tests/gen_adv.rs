use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i32>) -> (out: Vec<i32>)
    requires
        1 <= n <= 100,
        values.len() == 3 * n,
        forall|i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        1 <= n <= 100,
        out.len() == 3 * n,
        forall|i: int| 0 <= i < out.len() ==> -100 <= #[trigger] out[i] <= 100,
{
    let mut out: Vec<i32> = Vec::new();
    let total: usize = 3 * n;
    let mut i: usize = 0;
    while i < total
        invariant
            total == 3 * n,
            1 <= n <= 100,
            values.len() == 3 * n,
            i <= total,
            out.len() == i,
            forall|k: int| 0 <= k < values.len() ==> -100 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < out.len() ==> out[k] == values[k],
            forall|k: int| 0 <= k < out.len() ==> -100 <= #[trigger] out[k] <= 100,
        decreases total - i,
    {
        let v = values[i];
        assert(-100 <= v <= 100);
        out.push(v);
        i = i + 1;
    }
    out
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
    let target: usize = 200;
    let mut rng = Rng::new(6901);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Edges - boundaries
    for &n in &[1usize, 2, 50, 100] {
        emit(vec![(0, 0, 0); n], &mut seen, &mut out, &mut count);
        emit(vec![(100, 100, 100); n], &mut seen, &mut out, &mut count);
        emit(vec![(-100, -100, -100); n], &mut seen, &mut out, &mut count);
        emit(vec![(1, 0, 0); n], &mut seen, &mut out, &mut count);
    }

    // Pair up
    for _ in 0..50 {
        let n = rng.gen_range_usize(2, 100);
        let mut vecs: Vec<(i32, i32, i32)> = Vec::new();
        let mut sx = 0i32; let mut sy = 0i32; let mut sz = 0i32;
        for _ in 0..n - 1 {
            let x = rng.gen_range_i32(-100, 100);
            let y = rng.gen_range_i32(-100, 100);
            let z = rng.gen_range_i32(-100, 100);
            vecs.push((x, y, z));
            sx += x; sy += y; sz += z;
        }
        let x = (-sx).clamp(-100, 100);
        let y = (-sy).clamp(-100, 100);
        let z = (-sz).clamp(-100, 100);
        vecs.push((x, y, z));
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

