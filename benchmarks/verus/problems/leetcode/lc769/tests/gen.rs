use vstd::prelude::*;

verus! {

pub fn valid_permutation(raw: &Vec<i32>) -> (valid: bool)
    ensures valid ==> (
        1 <= raw.len() <= 10
        && (forall|i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] < raw.len())
        && (forall|i: int, j: int| 0 <= i < j < raw.len() ==> raw[i] != raw[j])),
{
    if raw.len() == 0 || raw.len() > 10 { return false; }
    let mut i = 0usize;
    while i < raw.len()
        invariant
            1 <= raw.len() <= 10, 0 <= i <= raw.len(),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] raw[j] < raw.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> raw[j] != raw[k],
        decreases raw.len() - i,
    {
        if raw[i] < 0 || raw[i] as usize >= raw.len() { return false; }
        let mut j = 0usize;
        while j < i
            invariant
                0 <= j <= i < raw.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] raw[k] != raw[i as int],
            decreases i - j,
        {
            if raw[j] == raw[i] { return false; }
            j += 1;
        }
        i += 1;
    }
    true
}

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 10,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] < result.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if valid_permutation(&raw) { return raw; }
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10 { 10usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 10, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == j,
        decreases n - i,
    {
        result.push(i as i32);
        i += 1;
    }
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 10, 0 <= i <= n, result.len() == n,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] < n,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { i as i32 };
        let j = if v < 0 || v as usize >= n { i } else { v as usize };
        let a = result[i];
        let b = result[j];
        result.set(i, b);
        result.set(j, a);
        i += 1;
    }
    result
}


pub fn generate_candidate(n: usize, swap_a: usize, swap_b: usize, mutation_kind: u8) -> (arr: Vec<i32>)
    requires
        1 <= n <= 10,
        swap_a < n,
        swap_b < n,
    ensures
        1 <= arr.len() <= 10,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] < arr.len(),
{
    // Build identity permutation [0, 1, ..., n-1]
    let mut arr: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            1 <= n <= 10,
            arr.len() == k,
            forall|j: int| 0 <= j < k ==> arr[j] == j as i32,
            forall|j: int| 0 <= j < k ==> 0 <= #[trigger] arr[j] < n,
        decreases n - k,
    {
        arr.push(k as i32);
        k += 1;
    }

    if mutation_kind == 0 {
        // identity permutation (sorted) — max chunks = n
        arr
    } else if mutation_kind == 1 {
        // swap two elements
        let tmp_a = arr[swap_a];
        let tmp_b = arr[swap_b];
        arr.set(swap_a, tmp_b);
        arr.set(swap_b, tmp_a);
        arr
    } else if mutation_kind == 2 {
        // reverse the array
        let mut i: usize = 0;
        while i < n / 2
            invariant
                arr.len() == n,
                1 <= n <= 10,
                0 <= i <= n / 2,
                forall|j: int| 0 <= j < arr.len() ==> 0 <= #[trigger] arr[j] < n,
            decreases n / 2 - i,
        {
            let j = n - 1 - i;
            let tmp_i = arr[i];
            let tmp_j = arr[j];
            arr.set(i, tmp_j);
            arr.set(j, tmp_i);
            i += 1;
        }
        arr
    } else if mutation_kind == 3 {
        // set all elements to 0 (all same, still in [0, n))
        let mut i: usize = 0;
        while i < n
            invariant
                arr.len() == n,
                1 <= n <= 10,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> arr[j] == 0i32,
                forall|j: int| 0 <= j < arr.len() ==> 0 <= #[trigger] arr[j] < n,
            decreases n - i,
        {
            arr.set(i, 0);
            i += 1;
        }
        arr
    } else if mutation_kind == 4 && n >= 2 {
        // swap first and last elements
        let tmp_first = arr[0];
        let tmp_last = arr[n - 1];
        arr.set(0, tmp_last);
        arr.set(n - 1, tmp_first);
        arr
    } else if mutation_kind == 5 {
        // set element at swap_a to 0
        arr.set(swap_a, 0);
        arr
    } else if mutation_kind == 6 && n >= 2 {
        // move last element to front: [n-1, 0, 1, ..., n-2]
        let mut result: Vec<i32> = Vec::new();
        result.push((n - 1) as i32);
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                1 <= n <= 10,
                result.len() == i + 1,
                arr.len() == n,
                forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] < n,
                forall|j: int| 0 <= j < arr.len() ==> 0 <= #[trigger] arr[j] < n,
            decreases (n - 1) - i,
        {
            result.push(arr[i]);
            i += 1;
        }
        result
    } else {
        // fallback: identity
        arr
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        let arr = generate_test_case(arr);
        if *emitted >= count { return; }
        let key = format!("{:?}", arr);
        if !seen.insert(key) { return; }
        let output = Solution::max_chunks_to_sorted(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![4, 3, 2, 1, 0], &mut seen, &mut out, &mut emitted);
    emit(vec![1, 0, 2, 3, 4], &mut seen, &mut out, &mut emitted);

    // Systematic: identity permutations of each size
    for n in 1..=10usize {
        let arr = generate_candidate(n, 0, 0, 0);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }

    // Systematic: reversed permutations of each size
    for n in 1..=10usize {
        let arr = generate_candidate(n, 0, 0, 2);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }

    // Systematic: all-zeros of each size
    for n in 1..=10usize {
        let arr = generate_candidate(n, 0, 0, 3);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }

    // Systematic: rotate-left of each size >= 2
    for n in 2..=10usize {
        let arr = generate_candidate(n, 0, 0, 6);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }

    // Systematic: swap first/last for each size >= 2
    for n in 2..=10usize {
        let arr = generate_candidate(n, 0, 0, 4);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }

    // Random: vary n, swap positions, and mutation kinds
    let mut _attempts_0 = 0usize;
    while emitted < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n = rng.gen_range_usize(1, 10);
        let swap_a = rng.gen_range_usize(0, n - 1);
        let swap_b = rng.gen_range_usize(0, n - 1);
        let mutation_kind = rng.gen_range_usize(0, 6) as u8;
        let arr = generate_candidate(n, swap_a, swap_b, mutation_kind);
        emit(arr, &mut seen, &mut out, &mut emitted);
    }
}
