use vstd::prelude::*;

verus! {

pub open spec fn value_occurs(p: Seq<i32>, n: int, v: int) -> bool {
    exists|i: int| 0 <= i < n && p[i] == v
}

pub open spec fn is_permutation_1_to_n(p: Seq<i32>, n: int) -> bool {
    p.len() == n
        && 1 <= n <= 100
        && forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] <= n
        && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
        && forall|v: int| 1 <= v <= n ==> #[trigger] value_occurs(p, n, v)
}

pub fn generate_test_case(
    n: usize,
    swap_a: usize,
    swap_b: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 100,
        swap_a < n,
        swap_b < n,
    ensures
        1 <= result.1 <= 100,
        result.0.len() == result.1,
        is_permutation_1_to_n(result.0@, result.1 as int),
{
    // Build identity permutation [1, 2, ..., n]
    let mut p: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            p.len() == i,
            1 <= n <= 100,
            forall|j: int| 0 <= j < i as int ==> #[trigger] p@[j] == (j + 1) as i32,
        decreases n - i,
    {
        p.push((i + 1) as i32);
        i += 1;
    }

    // Prove identity permutation satisfies is_permutation_1_to_n
    proof {
        assert(p@.len() == n as int);

        // Range: p[i] = i + 1, so 1 <= p[i] <= n
        assert forall|i: int| 0 <= i < n as int implies 1 <= #[trigger] p@[i] <= n as int by {
            assert(p@[i] == (i + 1) as i32);
        }

        // Distinct: p[i] = i+1, so i != j => p[i] != p[j]
        assert forall|i: int, j: int| 0 <= i < j < n as int implies p@[i] != p@[j] by {
            assert(p@[i] == (i + 1) as i32);
            assert(p@[j] == (j + 1) as i32);
        }

        // value_occurs: witness i = v - 1
        assert forall|v: int| 1 <= v <= n as int implies #[trigger] value_occurs(p@, n as int, v) by {
            let witness = v - 1;
            assert(0 <= witness < n as int);
            assert(p@[witness] == v as i32);
        }
    }

    if mutation_kind == 1 && swap_a != swap_b {
        // Swap elements at positions swap_a and swap_b
        let va = p[swap_a];
        let vb = p[swap_b];

        // Record values before swap
        proof {
            assert(va == (swap_a as int + 1) as i32);
            assert(vb == (swap_b as int + 1) as i32);
        }

        p.set(swap_a, vb);
        p.set(swap_b, va);

        // Prove properties after swap
        proof {
            assert(p@.len() == n as int);

            // After swap: p[swap_a] = vb = swap_b+1, p[swap_b] = va = swap_a+1,
            // and for k != swap_a, swap_b: p[k] = k+1

            // Range
            assert forall|k: int| 0 <= k < n as int implies 1 <= #[trigger] p@[k] <= n as int by {
                if k == swap_a as int {
                    assert(p@[k] == vb);
                } else if k == swap_b as int {
                    assert(p@[k] == va);
                }
            }

            // Distinct
            assert forall|k1: int, k2: int| 0 <= k1 < k2 < n as int implies p@[k1] != p@[k2] by {
                if k1 == swap_a as int && k2 == swap_b as int {
                    // p[swap_a] = swap_b+1, p[swap_b] = swap_a+1
                    // swap_a != swap_b => swap_b+1 != swap_a+1
                } else if k1 == swap_a as int {
                    // p[swap_a] = swap_b+1, p[k2] = k2+1 (k2 != swap_b)
                    // swap_b != k2 => swap_b+1 != k2+1
                } else if k1 == swap_b as int && k2 == swap_a as int {
                    // Can't happen: k1 < k2 and k1 == swap_b, k2 == swap_a
                    // means swap_b < swap_a, but we handle it
                    // p[swap_b] = swap_a+1, p[swap_a] = swap_b+1
                } else if k1 == swap_b as int {
                    // p[swap_b] = swap_a+1, p[k2] != swap_a, != swap_b => p[k2] = k2+1
                    // swap_a != k2 => swap_a+1 != k2+1
                    if k2 == swap_a as int {
                        // p[swap_b] = swap_a+1, p[swap_a] = swap_b+1
                    }
                } else if k2 == swap_a as int {
                    // k1 != swap_a, k1 != swap_b
                    // p[k1] = k1+1, p[swap_a] = swap_b+1
                    // k1 != swap_b => k1+1 != swap_b+1
                } else if k2 == swap_b as int {
                    // k1 != swap_a, k1 != swap_b
                    // p[k1] = k1+1, p[swap_b] = swap_a+1
                    // k1 != swap_a => k1+1 != swap_a+1
                } else {
                    // Both unchanged: p[k1] = k1+1, p[k2] = k2+1
                }
            }

            // value_occurs
            assert forall|v: int| 1 <= v <= n as int implies #[trigger] value_occurs(p@, n as int, v) by {
                if v == swap_a as int + 1 {
                    // va = swap_a+1, placed at swap_b
                    assert(p@[swap_b as int] == v as i32);
                } else if v == swap_b as int + 1 {
                    // vb = swap_b+1, placed at swap_a
                    assert(p@[swap_a as int] == v as i32);
                } else {
                    // Unchanged: p[v-1] = v
                    let witness = v - 1;
                    assert(0 <= witness < n as int);
                    assert(witness != swap_a as int);
                    assert(witness != swap_b as int);
                    assert(p@[witness] == v as i32);
                }
            }
        }
    }

    (p, n)
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

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut p: Vec<i32> = (1..=(n as i32)).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        p.swap(i, j);
    }
    p
}

fn build_input(p: &[i32]) -> String {
    let mut s = format!("{}\n", p.len());
    let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(r: &[i32]) -> String {
    let parts: Vec<String> = r.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join(" ");
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |p: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>| {
        let n = p.len();
        let r = Solution::inverse_presents(p.clone(), n);
        let inp = build_input(&p);
        let outp = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    };

    // Examples
    emit(vec![2, 3, 4, 1], &mut out);
    emit(vec![1, 3, 2], &mut out);
    emit(vec![1, 2], &mut out);

    // Edge cases
    emit(vec![1], &mut out);
    emit((1..=100).collect(), &mut out); // identity
    emit((1..=100).rev().collect(), &mut out);

    let mut count = 6;
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(1, 30),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let p = random_perm(&mut rng, n);
        emit(p, &mut out);
        count += 1;
    }
}

