use vstd::prelude::*;

verus! {

/// Swap elements at two positions in a permutation vector.
/// Preserves length, value range [1, n], and element distinctness.
fn swap_in_perm(v: Vec<i32>, p: usize, q: usize) -> (result: Vec<i32>)
    requires
        1 <= v.len() <= 50,
        p < v.len(),
        q < v.len(),
        forall|i: int| 0 <= i < v.len() ==> 1 <= #[trigger] v[i] <= v.len(),
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j],
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if p == q {
        return v;
    }
    let mut w = v;
    let val_p = w[p];
    let val_q = w[q];
    w.set(p, val_q);
    w.set(q, val_p);

    proof {
        // Range: each position holds an original value that was in [1, v.len()]
        assert forall|k: int| 0 <= k < w.len() implies 1 <= #[trigger] w[k] <= w.len() by {
            if k == p as int {
                assert(w[k] == v[q as int]);
            } else if k == q as int {
                assert(w[k] == v[p as int]);
            } else {
                assert(w[k] == v[k]);
            }
        };

        // Distinctness: the transposition is a bijection on indices
        assert forall|i: int, j: int| 0 <= i < j < w.len() implies w[i] != w[j] by {
            if i == p as int && j == q as int {
                // w[p] = v[q], w[q] = v[p]; since p < q here (i < j)
                assert(v[p as int] != v[q as int]);
            } else if i == p as int {
                // w[p] = v[q], w[j] = v[j]; need v[q] != v[j], and q != j
                if (q as int) < j {
                    assert(v[q as int] != v[j]);
                } else {
                    assert(v[j] != v[q as int]);
                }
            } else if i == q as int && j == p as int {
                // w[q] = v[p], w[p] = v[q]; since q < p here (i < j)
                assert(v[q as int] != v[p as int]);
            } else if i == q as int {
                // w[q] = v[p], w[j] = v[j]; need v[p] != v[j], and p != j
                if (p as int) < j {
                    assert(v[p as int] != v[j]);
                } else {
                    assert(v[j] != v[p as int]);
                }
            } else if j == p as int {
                // w[i] = v[i], w[p] = v[q]; need v[i] != v[q], and i != q
                if i < (q as int) {
                    assert(v[i] != v[q as int]);
                } else {
                    assert(v[q as int] != v[i]);
                }
            } else if j == q as int {
                // w[i] = v[i], w[q] = v[p]; need v[i] != v[p], and i != p
                if i < (p as int) {
                    assert(v[i] != v[p as int]);
                } else {
                    assert(v[p as int] != v[i]);
                }
            } else {
                // Neither i nor j is p or q; w[i] = v[i], w[j] = v[j]
                assert(v[i] != v[j]);
            }
        };
    }

    w
}

pub fn generate_test_case(
    a: Vec<i32>,
    b: Vec<i32>,
    swap_a_i: usize,
    swap_a_j: usize,
    swap_b_i: usize,
    swap_b_j: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= a.len() <= 50,
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len(),
        forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= b.len(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] != a[j],
        forall|i: int, j: int| 0 <= i < j < b.len() ==> b[i] != b[j],
        swap_a_i < a.len(),
        swap_a_j < a.len(),
        swap_b_i < b.len(),
        swap_b_j < b.len(),
    ensures
        1 <= result.0.len() <= 50,
        result.1.len() == result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.0.len(),
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.1.len(),
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
{
    if mutation_kind == 1 {
        // Swap two elements in a only
        let ra = swap_in_perm(a, swap_a_i, swap_a_j);
        (ra, b)
    } else if mutation_kind == 2 {
        // Swap two elements in b only
        let rb = swap_in_perm(b, swap_b_i, swap_b_j);
        (a, rb)
    } else if mutation_kind == 3 {
        // Swap in both a and b
        let ra = swap_in_perm(a, swap_a_i, swap_a_j);
        let rb = swap_in_perm(b, swap_b_i, swap_b_j);
        (ra, rb)
    } else {
        // Identity (pass-through)
        (a, b)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut perm: Vec<i32> = (1..=(n as i32)).collect();
    // Fisher-Yates shuffle
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        perm.swap(i, j);
    }
    perm
}

fn mutate(
    a: Vec<i32>, b: Vec<i32>,
    sai: usize, saj: usize, sbi: usize, sbj: usize,
    mk: u8,
) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(a, b, sai, saj, sbi, sbj, mk)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2657);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |a: Vec<i32>, b: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?},{:?}", a, b);
        if !seen.insert(key) { return; }
        let output = Solution::find_the_prefix_common_array(a.clone(), b.clone());
        writeln!(out, "{}", json!({
            "input": {"a": a, "b": b},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description
    emit(vec![1,3,2,4], vec![3,1,2,4], &mut seen, &mut out, &mut total);
    emit(vec![2,3,1], vec![3,1,2], &mut seen, &mut out, &mut total);

    // Boundary: n=1
    emit(vec![1], vec![1], &mut seen, &mut out, &mut total);

    // Identity permutations of various sizes
    for n in [2, 3, 5, 10, 20, 50] {
        let id: Vec<i32> = (1..=(n as i32)).collect();
        emit(id.clone(), id, &mut seen, &mut out, &mut total);
    }

    // Reversed permutations
    for n in [2, 5, 10, 50] {
        let rev: Vec<i32> = (1..=(n as i32)).rev().collect();
        let id: Vec<i32> = (1..=(n as i32)).collect();
        emit(rev.clone(), id.clone(), &mut seen, &mut out, &mut total);
        emit(id, rev, &mut seen, &mut out, &mut total);
    }

    // Size classes with all mutation kinds
    let sizes = [1, 2, 3, 5, 10, 15, 20, 30, 40, 50];
    let mutation_kinds: [u8; 4] = [0, 1, 2, 3];

    for &n in &sizes {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let a = random_permutation(&mut rng, n);
            let b = random_permutation(&mut rng, n);
            let sai = rng.gen_range_usize(0, n - 1);
            let saj = rng.gen_range_usize(0, n - 1);
            let sbi = rng.gen_range_usize(0, n - 1);
            let sbj = rng.gen_range_usize(0, n - 1);
            let (ra, rb) = mutate(a, b, sai, saj, sbi, sbj, mk);
            emit(ra, rb, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with diverse random sizes and mutations
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 25),
            3 => rng.gen_range_usize(26, 40),
            _ => rng.gen_range_usize(41, 50),
        };
        let a = random_permutation(&mut rng, n);
        let b = random_permutation(&mut rng, n);
        let sai = rng.gen_range_usize(0, n - 1);
        let saj = rng.gen_range_usize(0, n - 1);
        let sbi = rng.gen_range_usize(0, n - 1);
        let sbj = rng.gen_range_usize(0, n - 1);
        let mk = (total % 4) as u8;
        let (ra, rb) = mutate(a, b, sai, saj, sbi, sbj, mk);
        emit(ra, rb, &mut seen, &mut out, &mut total);
    }
}
