use vstd::prelude::*;

verus! {

pub open spec fn value_in(s: Seq<i32>, v: i32) -> bool {
    exists |j: int| 0 <= j < s.len() && s[j] == v
}

/// Build a valid permutation of [1..n] using different construction strategies.
pub fn generate_test_case(n: usize, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= n <= 100,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==>
            1 <= #[trigger] result[i] <= result.len() as i32,
        forall |i: int, j: int|
            0 <= i < j < result.len() ==> result[i] != result[j],
        forall |v: i32| 1 <= v <= result.len() as i32 ==>
            #[trigger] value_in(result@, v),
{
    if mutation_kind == 1 {
        // Reversed: [n, n-1, ..., 1]
        let mut arr: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                arr.len() == k as int,
                forall |j: int| 0 <= j < k as int ==>
                    arr[j] == (n as int - j) as i32,
            decreases n - k,
        {
            arr.push((n - k) as i32);
            k += 1;
        }
        proof {
            assert(arr.len() == n as int);
            assert forall |i: int| 0 <= i < arr.len() implies
                1 <= #[trigger] arr[i] <= arr.len() as i32 by
            {
                assert(arr[i] == (n as int - i) as i32);
            };
            assert forall |i: int, j: int|
                0 <= i < j < arr.len() implies arr[i] != arr[j] by
            {
                assert(arr[i] == (n as int - i) as i32);
                assert(arr[j] == (n as int - j) as i32);
            };
            assert forall |v: i32| 1 <= v <= arr.len() as i32 implies
                #[trigger] value_in(arr@, v) by
            {
                let wit = n as int - v as int;
                assert(0 <= wit < arr.len());
                assert(arr[wit] == v);
            };
        }
        arr
    } else if mutation_kind == 2 && n >= 2 {
        // Swap first two: [2, 1, 3, 4, ..., n]
        let mut arr: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                arr.len() == k as int,
                forall |j: int| 0 <= j < k as int ==>
                    arr[j] == (j + 1) as i32,
            decreases n - k,
        {
            arr.push((k + 1) as i32);
            k += 1;
        }
        let tmp = arr[0];
        arr.set(0, arr[1]);
        arr.set(1, tmp);
        proof {
            assert(arr.len() == n as int);
            assert(arr[0int] == 2i32);
            assert(arr[1int] == 1i32);
            assert forall |j: int| 2 <= j < arr.len() implies
                arr[j] == (j + 1) as i32 by {};
            assert forall |i: int| 0 <= i < arr.len() implies
                1 <= #[trigger] arr[i] <= arr.len() as i32 by
            {
                if i == 0 {
                    assert(arr[i] == 2i32);
                } else if i == 1 {
                    assert(arr[i] == 1i32);
                } else {
                    assert(arr[i] == (i + 1) as i32);
                }
            };
            assert forall |i: int, j: int|
                0 <= i < j < arr.len() implies arr[i] != arr[j] by
            {
                if i == 0 && j == 1 {
                    assert(arr[i] == 2i32);
                    assert(arr[j] == 1i32);
                } else if i == 0 {
                    assert(arr[i] == 2i32);
                    assert(arr[j] == (j + 1) as i32);
                } else if i == 1 {
                    assert(arr[i] == 1i32);
                    assert(arr[j] == (j + 1) as i32);
                } else {
                    assert(arr[i] == (i + 1) as i32);
                    assert(arr[j] == (j + 1) as i32);
                }
            };
            assert forall |v: i32| 1 <= v <= arr.len() as i32 implies
                #[trigger] value_in(arr@, v) by
            {
                if v == 1i32 {
                    assert(arr[1int] == v);
                } else if v == 2i32 {
                    assert(arr[0int] == v);
                } else {
                    let wit = (v - 1) as int;
                    assert(arr[wit] == v);
                }
            };
        }
        arr
    } else if mutation_kind == 3 && n >= 2 {
        // Swap first and last: [n, 2, 3, ..., n-1, 1]
        let mut arr: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                arr.len() == k as int,
                forall |j: int| 0 <= j < k as int ==>
                    arr[j] == (j + 1) as i32,
            decreases n - k,
        {
            arr.push((k + 1) as i32);
            k += 1;
        }
        let last = n - 1;
        let tmp = arr[0];
        arr.set(0, arr[last]);
        arr.set(last, tmp);
        proof {
            assert(arr.len() == n as int);
            assert(arr[0int] == n as i32);
            assert(arr[(n - 1) as int] == 1i32);
            assert forall |j: int| 1 <= j < (n - 1) as int implies
                arr[j] == (j + 1) as i32 by {};
            assert forall |i: int| 0 <= i < arr.len() implies
                1 <= #[trigger] arr[i] <= arr.len() as i32 by
            {
                if i == 0 {
                    assert(arr[i] == n as i32);
                } else if i == (n - 1) as int {
                    assert(arr[i] == 1i32);
                } else {
                    assert(arr[i] == (i + 1) as i32);
                }
            };
            assert forall |i: int, j: int|
                0 <= i < j < arr.len() implies arr[i] != arr[j] by
            {
                if i == 0 && j == (n - 1) as int {
                    assert(arr[i] == n as i32);
                    assert(arr[j] == 1i32);
                } else if i == 0 {
                    assert(arr[i] == n as i32);
                    assert(arr[j] == (j + 1) as i32);
                } else if j == (n - 1) as int {
                    assert(arr[i] == (i + 1) as i32);
                    assert(arr[j] == 1i32);
                } else {
                    assert(arr[i] == (i + 1) as i32);
                    assert(arr[j] == (j + 1) as i32);
                }
            };
            assert forall |v: i32| 1 <= v <= arr.len() as i32 implies
                #[trigger] value_in(arr@, v) by
            {
                if v == n as i32 {
                    assert(arr[0int] == v);
                } else if v == 1i32 {
                    assert(arr[(n - 1) as int] == v);
                } else {
                    let wit = (v - 1) as int;
                    assert(arr[wit] == v);
                }
            };
        }
        arr
    } else {
        // Sorted: [1, 2, ..., n] (mutation_kind == 0 and fallback)
        let mut arr: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                arr.len() == k as int,
                forall |j: int| 0 <= j < k as int ==>
                    arr[j] == (j + 1) as i32,
            decreases n - k,
        {
            arr.push((k + 1) as i32);
            k += 1;
        }
        proof {
            assert(arr.len() == n as int);
            assert forall |i: int| 0 <= i < arr.len() implies
                1 <= #[trigger] arr[i] <= arr.len() as i32 by
            {
                assert(arr[i] == (i + 1) as i32);
            };
            assert forall |i: int, j: int|
                0 <= i < j < arr.len() implies arr[i] != arr[j] by
            {
                assert(arr[i] == (i + 1) as i32);
                assert(arr[j] == (j + 1) as i32);
            };
            assert forall |v: i32| 1 <= v <= arr.len() as i32 implies
                #[trigger] value_in(arr@, v) by
            {
                let wit = (v - 1) as int;
                assert(0 <= wit < arr.len());
                assert(arr[wit] == v);
            };
        }
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

/// Fisher-Yates shuffle to produce a random permutation of [1..n].
fn random_permutation(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut arr: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        arr.swap(i, j);
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(969);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::pancake_sort(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 4, 1],
        vec![1, 2, 3],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Apply all mutation kinds to various sizes
    let sizes: Vec<usize> = vec![1, 2, 3, 4, 5, 10, 20, 50, 100];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3];
    for &n in &sizes {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let arr = generate_test_case(n, mk);
            emit(arr, &mut seen, &mut out, &mut count);
        }
    }

    // Random permutations with random mutations
    for _ in 0..40 {
        if count >= target { break; }
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let arr = random_permutation(&mut rng, n);
        emit(arr, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random permutations
    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let arr = random_permutation(&mut rng, n);
        emit(arr, &mut seen, &mut out, &mut count);
    }
}
