use vstd::prelude::*;

verus! {

pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

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

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        deltas.len() >= 2,
        deltas.len() + 1 <= 100_000,
        0 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 100_000,
    ensures
        3 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
    }

    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == idx + 1,
            deltas.len() >= 2,
            deltas.len() + 1 <= 100_000,
            0 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 100_000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100_000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(0 <= next <= 100_000i32) by {
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        nums.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] < nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    if mutation_kind == 1 {
        let v0 = nums[0];
        let v1 = nums[1];
        let mut result = nums;
        result.set(0, v1);
        result.set(1, v0);
        proof {
            assert forall|i: int, j: int| 0 <= i < j < result.len()
                implies result[i] != result[j] by {
                let ni: int = if i == 0 { 1 } else if i == 1 { 0 } else { i };
                let nj: int = if j == 0 { 1 } else if j == 1 { 0 } else { j };
                assert(result[i] == nums[ni]);
                assert(result[j] == nums[nj]);
                if ni < nj { assert(nums[ni] < nums[nj]); }
                else { assert(nums[nj] < nums[ni]); }
            };
        }
        result
    } else if mutation_kind == 2 {
        let last = nums.len() - 1;
        let prev = nums.len() - 2;
        let vl = nums[last];
        let vp = nums[prev];
        let mut result = nums;
        result.set(prev, vl);
        result.set(last, vp);
        proof {
            let p = prev as int;
            let l = last as int;
            assert forall|i: int, j: int| 0 <= i < j < result.len()
                implies result[i] != result[j] by {
                let ni: int = if i == p { l } else if i == l { p } else { i };
                let nj: int = if j == p { l } else if j == l { p } else { j };
                assert(result[i] == nums[ni]);
                assert(result[j] == nums[nj]);
                if ni < nj { assert(nums[ni] < nums[nj]); }
                else { assert(nums[nj] < nums[ni]); }
            };
        }
        result
    } else if mutation_kind == 3 {
        let last = nums.len() - 1;
        let v0 = nums[0];
        let vl = nums[last];
        let mut result = nums;
        result.set(0, vl);
        result.set(last, v0);
        proof {
            let l = last as int;
            assert forall|i: int, j: int| 0 <= i < j < result.len()
                implies result[i] != result[j] by {
                let ni: int = if i == 0 { l } else if i == l { 0 } else { i };
                let nj: int = if j == 0 { l } else if j == l { 0 } else { j };
                assert(result[i] == nums[ni]);
                assert(result[j] == nums[nj]);
                if ni < nj { assert(nums[ni] < nums[nj]); }
                else { assert(nums[nj] < nums[ni]); }
            };
        }
        result
    } else {
        proof {
            assert forall|i: int, j: int| 0 <= i < j < nums.len()
                implies nums[i] != nums[j] by {
                assert(nums[i] < nums[j]);
            };
        }
        nums
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

fn make_deltas(rng: &mut Rng, len: usize, max_val: i64) -> (Vec<i32>, i32) {
    let n_deltas = len - 1;
    let mut deltas = Vec::with_capacity(n_deltas);
    let mut total: i64 = 0;
    for _ in 0..n_deltas {
        let remaining = max_val - total - (n_deltas as i64 - deltas.len() as i64 - 1);
        let hi = std::cmp::min(remaining, 100).max(1);
        let d = rng.gen_range_i64(1, hi) as i32;
        deltas.push(d);
        total += d as i64;
    }
    let max_base = (100_000i64 - total).max(0);
    let base = rng.gen_range_i64(0, max_base) as i32;
    (deltas, base)
}

fn gen(deltas: &Vec<i32>, base: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(deltas, base, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1968);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", &nums);
        if !seen.insert(key) { return; }
        let result = Solution::rearrange_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        *emitted += 1;
    };

    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![6, 2, 0, 9, 7],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    let structured_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 1, 1, 1], 0),
        (vec![1, 1], 0),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1], 0),
        (vec![10, 10, 10, 10], 0),
        (vec![1, 1, 1, 1], 99_996),
        (vec![100, 100], 0),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 50_000),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3];

    for (deltas, base) in &structured_seeds {
        for mk in &mutation_kinds {
            if emitted >= count { break; }
            let result = gen(deltas, *base, *mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![
        (3, 5), (6, 20), (21, 100), (101, 500), (501, 1000),
    ];

    for class_idx in 0..size_classes.len() {
        let (lo, hi) = size_classes[class_idx];
        for _ in 0..12 {
            if emitted >= count { break; }
            let len = rng.gen_range_usize(lo, hi);
            let (deltas, base) = make_deltas(&mut rng, len, 100_000);
            let mk = rng.gen_range_usize(0, 3) as u8;
            let result = gen(&deltas, base, mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    while emitted < count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 20),
            2 => rng.gen_range_usize(20, 200),
            3 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(3, 500),
        };
        let (deltas, base) = make_deltas(&mut rng, len, 100_000);
        let mk = rng.gen_range_usize(0, 3) as u8;
        let result = gen(&deltas, base, mk);
        emit(result, &mut seen, &mut out, &mut emitted);
    }
}
