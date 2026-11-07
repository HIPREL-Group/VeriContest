use vstd::prelude::*;

verus! {

struct Gen;

impl Gen {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    proof fn lemma_count_all_same(s: Seq<i32>, v: i32)
        requires forall|i: int| 0 <= i < s.len() ==> s[i] == v,
        ensures Self::count(s, v) == s.len(),
        decreases s.len(),
    {
        if s.len() > 0 {
            let sub = s.subrange(1, s.len() as int);
            assert forall|i: int| 0 <= i < sub.len() implies sub[i] == v by {
                assert(sub[i] == s[i + 1]);
            };
            Self::lemma_count_all_same(sub, v);
        }
    }

    proof fn lemma_count_other_zero(s: Seq<i32>, v: i32, w: i32)
        requires
            forall|i: int| 0 <= i < s.len() ==> s[i] == v,
            w != v,
        ensures Self::count(s, w) == 0,
        decreases s.len(),
    {
        if s.len() > 0 {
            let sub = s.subrange(1, s.len() as int);
            assert forall|i: int| 0 <= i < sub.len() implies sub[i] == v by {
                assert(sub[i] == s[i + 1]);
            };
            Self::lemma_count_other_zero(sub, v, w);
        }
    }

    /// Build a sorted array of n copies of val, with mutations on parameters.
    pub fn generate_test_case(n: usize, val: i32, mutation_kind: u8) -> (arr: Vec<i32>)
        requires
            1 <= n <= 10_000,
            0 <= val <= 100_000,
        ensures
            1 <= arr.len() <= 10_000,
            forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000,
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
            exists|v: i32| #[trigger] Self::count(arr@, v) > arr.len() as int / 4,
            forall|v1: i32, v2: i32| (Self::count(arr@, v1) > arr.len() as int / 4
                && Self::count(arr@, v2) > arr.len() as int / 4) ==> v1 == v2,
    {
        // Mutate the value parameter
        let actual_val: i32 = if mutation_kind == 1 && val < 100_000 {
            val + 1
        } else if mutation_kind == 2 && val > 0 {
            val - 1
        } else if mutation_kind == 3 {
            0i32
        } else if mutation_kind == 4 {
            100_000i32
        } else if mutation_kind == 9 {
            val / 2
        } else {
            val
        };

        // Mutate the length parameter
        let actual_n: usize = if mutation_kind == 5 && n >= 2 {
            n / 2
        } else if mutation_kind == 6 && n <= 5000 {
            n * 2
        } else if mutation_kind == 7 {
            1
        } else if mutation_kind == 8 {
            10_000
        } else {
            n
        };

        // Build array of actual_n copies of actual_val
        let mut arr: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < actual_n
            invariant
                0 <= i <= actual_n,
                1 <= actual_n <= 10_000,
                0 <= actual_val <= 100_000,
                arr.len() == i as int,
                forall|j: int| 0 <= j < i as int ==> arr[j] == actual_val,
            decreases actual_n - i,
        {
            arr.push(actual_val);
            i = i + 1;
        }

        proof {
            Self::lemma_count_all_same(arr@, actual_val);
            assert(Self::count(arr@, actual_val) == arr.len() as int);
            assert(Self::count(arr@, actual_val) > arr.len() as int / 4);

            assert forall|v1: i32, v2: i32|
                Self::count(arr@, v1) > arr.len() as int / 4
                && Self::count(arr@, v2) > arr.len() as int / 4
                implies v1 == v2 by {
                if v1 != actual_val {
                    Self::lemma_count_other_zero(arr@, actual_val, v1);
                }
                if v2 != actual_val {
                    Self::lemma_count_other_zero(arr@, actual_val, v2);
                }
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

/// Build a sorted array of length `n` with values in [0, 100000]
/// where `special_val` appears `special_count` times (> n/4).
fn build_sorted_array(rng: &mut Rng, n: usize, special_val: i32, special_count: usize) -> Vec<i32> {
    let quarter = n / 4;
    let other_count = n - special_count;

    let mut arr = Vec::with_capacity(n);
    for _ in 0..special_count {
        arr.push(special_val);
    }

    let mut counts = std::collections::HashMap::new();
    let mut filled = 0usize;
    while filled < other_count {
        let v = rng.gen_range_i64(0, 100000) as i32;
        if v == special_val { continue; }
        let c = counts.entry(v).or_insert(0usize);
        if *c < quarter {
            *c += 1;
            arr.push(v);
            filled += 1;
        }
    }

    arr.sort();
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1287);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", arr);
        if !seen.insert(key) { return; }
        let output = Solution::find_special_integer(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 2, 6, 6, 6, 6, 7, 10],
        vec![1, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted edge cases
    let crafted: Vec<Vec<i32>> = vec![
        vec![0],
        vec![100000],
        vec![5, 5],
        vec![0, 0, 0, 1],
        vec![1, 2, 2, 2],
        vec![0, 1, 1, 1, 2],
        vec![42, 42, 42, 42],
        vec![0, 0, 0, 0, 0],
        vec![100000, 100000, 100000, 100000],
    ];
    for s in &crafted {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    // Generator-based: diverse (n, val, mutation_kind) combinations
    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Boundary values for val
    let boundary_vals: Vec<i32> = vec![0, 1, 2, 50000, 99999, 100000];
    for bv in &boundary_vals {
        for mk in &mutation_kinds {
            let n = rng.gen_range_usize(1, 100);
            let result = Gen::generate_test_case(n, *bv, *mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random generator calls across size classes
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 4),
            1 => rng.gen_range_usize(4, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 5000),
        };
        let val = rng.gen_range_i64(0, 100000) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = Gen::generate_test_case(n, val, mk);
        emit(result, &mut seen, &mut out, &mut count);

        // Also emit a structurally diverse array via build_sorted_array
        if count < target {
            let n2 = rng.gen_range_usize(1, 10000);
            let sv = rng.gen_range_i64(0, 100000) as i32;
            let min_c = n2 / 4 + 1;
            let sc = rng.gen_range_usize(min_c, n2);
            let arr = build_sorted_array(&mut rng, n2, sv, sc);
            emit(arr, &mut seen, &mut out, &mut count);
        }
    }
}
