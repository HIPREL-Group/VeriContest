use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] == 0 || a[i] == 1,
        exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0 || result[i] == 1,
        exists|i: int| 0 <= i < result.len() && #[trigger] result[i] == 0,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = a;
        d.set(0, 0);
        assert(d[0] == 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 0
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 0);
        assert(d[last as int] == 0);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        assert(d[0] == 0);
        d
    } else if mutation_kind == 4 {
        // set all elements to 1, then set first to 0 (single zero)
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d.set(0, 0);
        assert(d[0] == 0);
        d
    } else if mutation_kind == 5 && a.len() < 200_000 {
        // grow by one element (push 0)
        let mut d = a;
        d.push(0);
        proof {
            let new_last = (d.len() - 1) as int;
            assert(d[new_last] == 0);
        }
        d
    } else if mutation_kind == 6 && a.len() < 200_000 {
        // grow by one element (push 1)
        let mut d = a;
        d.push(1);
        proof {
            // the original a had a 0, which is still present
            let ghost zero_idx = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0;
            assert(d[zero_idx] == 0);
        }
        d
    } else if mutation_kind == 7 && a.len() > 1 && a[0] == 0 {
        // shrink by one element (pop), safe because a[0]==0 remains
        let mut d = a;
        d.pop();
        assert(d[0] == 0);
        d
    } else if mutation_kind == 8 {
        // set first element to 1 (if safe: need another 0 in array)
        // fallback to identity if len == 1
        if a.len() > 1 && a[a.len() - 1] == 0 {
            let mut d = a;
            d.set(0, 1);
            let last = d.len() - 1;
            assert(d[last as int] == 0);
            d
        } else {
            a
        }
    } else if mutation_kind == 9 {
        // flip last element
        let mut d = a;
        let last = d.len() - 1;
        if d[last] == 0 {
            // flip to 1, need another 0
            proof {
                let ghost zero_idx = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == 0;
                if zero_idx != last as int {
                    assert(d[zero_idx] == 0);
                }
            }
            if last > 0 && d[0] == 0 {
                d.set(last, 1);
                assert(d[0] == 0);
                d
            } else {
                d // can't safely flip, keep identity
            }
        } else {
            d.set(last, 0);
            assert(d[last as int] == 0);
            d
        }
    } else {
        // fallback: identity
        a
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
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn ensure_zero(v: &mut Vec<i32>) {
    if !v.iter().any(|&x| x == 0) {
        v[0] = 0;
    }
}

fn random_array_with_zero(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..len).map(|_| rng.gen_range_i32(0, 1)).collect();
    ensure_zero(&mut v);
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !a.iter().any(|&x| x == 0) { return; } // problem requires at least one 0
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let ans = Solution::maximal_continuous_rest(a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![1,0,1,0,1], &mut seen, &mut out, &mut count);
    emit(vec![0,1,0,1,1,0], &mut seen, &mut out, &mut count);
    emit(vec![1,0,1,1,1,0,1,1,1,1], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![0,1], &mut seen, &mut out, &mut count);
    emit(vec![1,0], &mut seen, &mut out, &mut count);
    emit(vec![0,1,1,1,1], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,1,0], &mut seen, &mut out, &mut count);
    emit(vec![0,0,0,0,0], &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,1,0,1,1,1,1], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 2000),
        };
        let v = random_array_with_zero(&mut rng, n);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

