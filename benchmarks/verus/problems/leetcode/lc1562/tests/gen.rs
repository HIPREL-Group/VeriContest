use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m_param: i32,
    swap_a: usize,
    swap_b: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        1 <= m_param <= n as i32,
        swap_a < n,
        swap_b < n,
    ensures
        result.0.len() >= 1,
        result.0.len() <= 100_000,
        1 <= result.1 <= result.0.len() as i32,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.0.len() as i32,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
{
    // Build identity permutation [1, 2, ..., n]
    let mut arr: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            1 <= n <= 100_000,
            arr.len() == k as nat,
            forall |i: int| 0 <= i < k as int ==> arr@[i] == (i + 1) as i32,
        decreases n - k,
    {
        arr.push((k + 1) as i32);
        k += 1;
    }

    // Optionally swap two positions (preserves permutation invariant)
    if swap_a != swap_b {
        let ghost pre = arr@;
        let va = arr[swap_a];
        let vb = arr[swap_b];
        assert(va == pre[swap_a as int]);
        assert(vb == pre[swap_b as int]);

        arr.set(swap_a, vb);
        arr.set(swap_b, va);

        proof {
            assert forall |i: int| 0 <= i < n as int
                implies 1 <= #[trigger] arr@[i] <= n as i32
            by {
                if i == swap_a as int {
                    assert(arr@[i] == vb);
                    assert(vb == pre[swap_b as int]);
                    assert(pre[swap_b as int] == (swap_b as int + 1) as i32);
                } else if i == swap_b as int {
                    assert(arr@[i] == va);
                    assert(va == pre[swap_a as int]);
                    assert(pre[swap_a as int] == (swap_a as int + 1) as i32);
                } else {
                    assert(arr@[i] == pre[i]);
                    assert(pre[i] == (i + 1) as i32);
                }
            };

            assert forall |i: int, j: int| 0 <= i < j < n as int
                implies arr@[i] != arr@[j]
            by {
                // Determine the mapped index for i
                let mi: int = if i == swap_a as int { swap_b as int }
                    else if i == swap_b as int { swap_a as int }
                    else { i };
                // Determine the mapped index for j
                let mj: int = if j == swap_a as int { swap_b as int }
                    else if j == swap_b as int { swap_a as int }
                    else { j };

                // arr[i] = pre[mi] = (mi + 1) as i32
                if i == swap_a as int {
                    assert(arr@[i] == vb);
                    assert(vb == pre[swap_b as int]);
                } else if i == swap_b as int {
                    assert(arr@[i] == va);
                    assert(va == pre[swap_a as int]);
                } else {
                    assert(arr@[i] == pre[i]);
                }
                assert(arr@[i] == pre[mi]);
                assert(pre[mi] == (mi + 1) as i32);

                // arr[j] = pre[mj] = (mj + 1) as i32
                if j == swap_a as int {
                    assert(arr@[j] == vb);
                    assert(vb == pre[swap_b as int]);
                } else if j == swap_b as int {
                    assert(arr@[j] == va);
                    assert(va == pre[swap_a as int]);
                } else {
                    assert(arr@[j] == pre[j]);
                }
                assert(arr@[j] == pre[mj]);
                assert(pre[mj] == (mj + 1) as i32);

                // The swap mapping is injective: mi != mj
                // Case analysis shows this for all combinations
                if i == swap_a as int && j == swap_b as int {
                    assert(mi == swap_b as int && mj == swap_a as int);
                } else if i == swap_a as int {
                    assert(mi == swap_b as int && mj == j);
                    // j != swap_b (else branch above), so mj = j != swap_b = mi
                } else if i == swap_b as int {
                    if j == swap_a as int {
                        assert(mi == swap_a as int && mj == swap_b as int);
                    } else {
                        assert(mi == swap_a as int && mj == j);
                        // j != swap_a (else branch), so mj = j != swap_a = mi
                    }
                } else {
                    if j == swap_a as int {
                        assert(mi == i && mj == swap_b as int);
                        // i != swap_b (else branch on i), so mi = i != swap_b = mj
                    } else if j == swap_b as int {
                        assert(mi == i && mj == swap_a as int);
                        // i != swap_a (else branch on i), so mi = i != swap_a = mj
                    } else {
                        assert(mi == i && mj == j);
                        // i != j since i < j
                    }
                }
                assert(mi != mj);
                // (mi + 1) as i32 != (mj + 1) as i32 since mi != mj and both in [0, 100_000)
            };
        }
    } else {
        proof {
            assert forall |i: int| 0 <= i < n as int
                implies 1 <= #[trigger] arr@[i] <= n as i32
            by {
                assert(arr@[i] == (i + 1) as i32);
            };

            assert forall |i: int, j: int| 0 <= i < j < n as int
                implies arr@[i] != arr@[j]
            by {
                assert(arr@[i] == (i + 1) as i32);
                assert(arr@[j] == (j + 1) as i32);
            };
        }
    }

    // Mutate m
    let m_out: i32 = if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        n as i32
    } else if mutation_kind == 3 && m_param < n as i32 {
        m_param + 1
    } else if mutation_kind == 4 && m_param > 1 {
        m_param - 1
    } else {
        m_param
    };

    (arr, m_out)
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

struct Solution;
include!("../code.rs");

/// Fisher-Yates shuffle to produce a random permutation of [1..=n]
fn random_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut perm: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        perm.swap(i, j);
    }
    perm
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1562);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut num = 0usize;

    let mut emit = |arr: Vec<i32>, m: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    num: &mut usize| {
        if *num >= count { return; }
        let key = format!("{:?},{}", arr, m);
        if !seen.insert(key) { return; }
        let output = Solution::find_latest_step(arr.clone(), m);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "m": m},
            "output": output
        })).unwrap();
        *num += 1;
    };

    // Example test cases from description.md
    {
        let arr = vec![3, 5, 1, 2, 4];
        emit(arr, 1, &mut seen, &mut out, &mut num);
    }
    {
        let arr = vec![3, 1, 5, 4, 2];
        emit(arr, 2, &mut seen, &mut out, &mut num);
    }

    // Edge cases: n = 1
    {
        let (arr, m) = generate_test_case(1, 1, 0, 0, 0);
        emit(arr, m, &mut seen, &mut out, &mut num);
    }

    // Edge cases: n = 2, various m
    for mk in 0..=4u8 {
        let (arr, m) = generate_test_case(2, 1, 0, 1, mk);
        emit(arr, m, &mut seen, &mut out, &mut num);
    }
    for mk in 0..=4u8 {
        let (arr, m) = generate_test_case(2, 2, 0, 1, mk);
        emit(arr, m, &mut seen, &mut out, &mut num);
    }

    // Structured test cases with identity/swapped permutations
    let structured_sizes: Vec<usize> = vec![3, 4, 5, 8, 10, 15, 20, 50, 100];
    for &n in &structured_sizes {
        if num >= count { break; }
        let m_vals: Vec<i32> = vec![1, (n / 2).max(1) as i32, n as i32];
        for &m in &m_vals {
            for mk in 0..=4u8 {
                if num >= count { break; }
                let sa = rng.gen_range_usize(0, n - 1);
                let sb = rng.gen_range_usize(0, n - 1);
                let (arr, m_out) = generate_test_case(n, m, sa, sb, mk);
                emit(arr, m_out, &mut seen, &mut out, &mut num);
            }
        }
    }

    // Random test cases with Fisher-Yates permutations
    while num < count {
        // Diverse size classes
        let n: usize = match num % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(5, 20),      // small
            2 => rng.gen_range_usize(20, 100),    // medium
            3 => rng.gen_range_usize(100, 500),   // large
            _ => rng.gen_range_usize(500, 1000),  // very large
        };

        let m: i32 = if num % 10 == 0 {
            1
        } else if num % 10 == 1 {
            n as i32
        } else {
            rng.gen_range_i64(1, n as i64) as i32
        };

        // Use Fisher-Yates for a truly random permutation
        let arr = random_permutation(&mut rng, n);

        emit(arr, m, &mut seen, &mut out, &mut num);
    }
}
