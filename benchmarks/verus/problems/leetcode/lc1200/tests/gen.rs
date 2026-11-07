use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 1.
proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// Two partial sums differ by at least (b - a) when every delta >= 1.
proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

pub fn generate_test_case(base: i32, deltas: &Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= deltas.len() <= 99_999,
        -1_000_000 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000 <= #[trigger] result[i] <= 1_000_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    // Build strictly sorted array: arr[k] = base + sum_deltas(deltas, k)
    let mut arr: Vec<i32> = Vec::new();
    arr.push(base);

    let mut idx: usize = 0;
    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
    }

    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            arr.len() == idx + 1,
            1 <= deltas.len() <= 99_999,
            -1_000_000 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] arr[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < arr.len() ==> -1_000_000 <= #[trigger] arr[k] <= 1_000_000,
            forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l],
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = arr[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(-1_000_000 <= next <= 1_000_000) by {
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
            };
            assert forall|k: int| 0 <= k < arr.len() implies arr[k] < next by {
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        let ghost old_len = arr.len();
        arr.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr[k] < arr[l] by {
                if l < old_len as int {
                } else {
                    assert(arr[l] == next);
                }
            };
        }
    }

    // arr is now strictly sorted => all elements distinct and in range.
    // Apply mutations that preserve distinctness and bounds.

    if mutation_kind == 1 {
        // Swap first and last elements
        let ghost old_seq = arr@;
        let last = arr.len() - 1;
        let v0 = arr[0];
        let vl = arr[last];
        arr.set(0, vl);
        arr.set(last, v0);

        proof {
            assert forall|k: int| 0 <= k < arr.len()
                implies -1_000_000 <= #[trigger] arr[k] <= 1_000_000 by {
                if k == 0 {
                    assert(arr[k] == vl);
                } else if k == last as int {
                    assert(arr[k] == v0);
                } else {
                    assert(arr[k] == old_seq[k]);
                }
            };

            assert forall|k: int, l: int| 0 <= k < l < arr.len()
                implies arr[k] != arr[l] by {
                if k == 0 && l == last as int {
                    assert(arr[k] == vl);
                    assert(arr[l] == v0);
                    assert(old_seq[0] < old_seq[last as int]);
                } else if k == 0 {
                    assert(arr[k] == vl);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[l] < old_seq[last as int]);
                } else if l == last as int {
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == v0);
                    assert(old_seq[0] < old_seq[k]);
                } else {
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[k] < old_seq[l]);
                }
            };
        }

        arr
    } else if mutation_kind == 2 && arr.len() >= 3 {
        // Swap first two elements
        let ghost old_seq = arr@;
        let v0 = arr[0];
        let v1 = arr[1];
        arr.set(0, v1);
        arr.set(1, v0);

        proof {
            assert forall|k: int| 0 <= k < arr.len()
                implies -1_000_000 <= #[trigger] arr[k] <= 1_000_000 by {
                if k == 0 {
                    assert(arr[k] == v1);
                } else if k == 1 {
                    assert(arr[k] == v0);
                } else {
                    assert(arr[k] == old_seq[k]);
                }
            };

            assert forall|k: int, l: int| 0 <= k < l < arr.len()
                implies arr[k] != arr[l] by {
                if k == 0 && l == 1 {
                    assert(arr[k] == v1);
                    assert(arr[l] == v0);
                    assert(old_seq[0] < old_seq[1]);
                } else if k == 0 {
                    assert(arr[k] == v1);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[1] < old_seq[l]);
                } else if k == 1 {
                    assert(arr[k] == v0);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[0] < old_seq[l]);
                } else {
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[k] < old_seq[l]);
                }
            };
        }

        arr
    } else if mutation_kind == 3 && arr.len() >= 3 {
        // Swap last two elements
        let ghost old_seq = arr@;
        let last = arr.len() - 1;
        let prev = last - 1;
        let vl = arr[last];
        let vp = arr[prev];
        arr.set(prev, vl);
        arr.set(last, vp);

        proof {
            assert forall|k: int| 0 <= k < arr.len()
                implies -1_000_000 <= #[trigger] arr[k] <= 1_000_000 by {
                if k == prev as int {
                    assert(arr[k] == vl);
                } else if k == last as int {
                    assert(arr[k] == vp);
                } else {
                    assert(arr[k] == old_seq[k]);
                }
            };

            assert forall|k: int, l: int| 0 <= k < l < arr.len()
                implies arr[k] != arr[l] by {
                if k == prev as int && l == last as int {
                    assert(arr[k] == vl);
                    assert(arr[l] == vp);
                    assert(old_seq[prev as int] < old_seq[last as int]);
                } else if k == prev as int {
                    // k = prev, l > prev, l != last => impossible since last = prev + 1
                    assert(false);
                } else if l == last as int {
                    // k < last, k != prev => k < prev
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == vp);
                    assert(old_seq[k] < old_seq[prev as int]);
                } else if l == prev as int {
                    // k < prev
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == vl);
                    assert(old_seq[k] < old_seq[last as int]);
                } else {
                    assert(arr[k] == old_seq[k]);
                    assert(arr[l] == old_seq[l]);
                    assert(old_seq[k] < old_seq[l]);
                }
            };
        }

        arr
    } else {
        // Identity: return sorted array
        arr
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_d as i64) as i32);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1200);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let mut key_arr = arr.clone();
        key_arr.sort();
        let key = format!("{:?}", key_arr);
        if !seen.insert(key) { return; }
        let output = Solution::minimum_abs_difference(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![4, 2, 1, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 3, 6, 10, 15], &mut seen, &mut out, &mut count);
    emit(vec![3, 8, -10, 23, 19, -4, -14, 27], &mut seen, &mut out, &mut count);

    macro_rules! gen_emit {
        ($base:expr, $deltas:expr, $mk:expr) => {
            {
                let arr = generate_test_case($base, &$deltas, $mk);
                emit(arr, &mut seen, &mut out, &mut count);
            }
        };
    }

    // Hand-crafted seeds: uniform spacing
    gen_emit!(0, vec![1; 2], 0);                    // [0,1,2]
    gen_emit!(-1_000_000, vec![1; 3], 0);            // consecutive from min
    gen_emit!(999_997, vec![1; 3], 0);               // consecutive near max
    gen_emit!(0, vec![1; 9], 0);                     // 10 consecutive
    gen_emit!(-5, vec![1; 10], 0);                   // 11 consecutive
    gen_emit!(0, vec![500_000; 1], 0);               // [0, 500000] large gap
    gen_emit!(-500_000, vec![1_000_000; 1], 0);      // [-500000, 500000]
    gen_emit!(0, vec![1; 1], 1);                     // [0,1] swapped -> [1,0]
    gen_emit!(0, vec![1, 2, 3], 1);                  // swap first/last
    gen_emit!(0, vec![1, 1, 1, 1], 2);               // swap first two
    gen_emit!(0, vec![1, 1, 1, 1], 3);               // swap last two

    // Tiny arrays (2-5 elements), all mutations
    for _ in 0..6 {
        let n = rng.gen_range_usize(2, 5);
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 500));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        for mk in 0u8..=3 {
            gen_emit!(base, deltas.clone(), mk);
        }
    }

    // Small arrays (6-20 elements), varied deltas
    for _ in 0..8 {
        let n = rng.gen_range_usize(6, 20);
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 200));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        gen_emit!(base, deltas, mk);
    }

    // Medium arrays (50-500 elements), mixed deltas
    for _ in 0..8 {
        let n = rng.gen_range_usize(50, 500);
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        gen_emit!(base, deltas, mk);
    }

    // Large arrays (1000-10000 elements), delta=1
    for _ in 0..4 {
        let n = rng.gen_range_usize(1000, 10000);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        gen_emit!(base, deltas, mk);
    }

    // Maximum size (100000 elements), delta=1
    {
        let deltas = vec![1i32; 99_999];
        let base = -50_000i32;
        gen_emit!(base, deltas.clone(), 0);
        gen_emit!(base, deltas.clone(), 1);
    }

    // Arrays with varied gap patterns (some close pairs, some large gaps)
    for _ in 0..6 {
        let n = rng.gen_range_usize(5, 50);
        let mut deltas = Vec::new();
        for j in 0..n - 1 {
            // Mix: some deltas = 1, some large
            if j % 3 == 0 {
                deltas.push(1i32);
            } else {
                let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
                deltas.push(rng.gen_range_i64(1, std::cmp::min(max_d, 100) as i64) as i32);
            }
        }
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        gen_emit!(base, deltas, mk);
    }

    // Fill remaining with random sizes and mutations
    while count < goal {
        let n = rng.gen_range_usize(2, 500);
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total);
        let base = if hi < -1_000_000 { -1_000_000i32 } else {
            rng.gen_range_i64(-1_000_000, hi) as i32
        };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        gen_emit!(base, deltas, mk);
    }
}
