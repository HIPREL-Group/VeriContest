use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    proof fn count_nonneg(s: Seq<i32>, v: i32)
        ensures Self::count(s, v) >= 0
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_nonneg(s.subrange(1, s.len() as int), v);
        }
    }

    proof fn count_contains(s: Seq<i32>, v: i32, k: int)
        requires
            0 <= k < s.len(),
            s[k] == v,
        ensures
            Self::count(s, v) >= 1
        decreases k
    {
        if k == 0 {
            Self::count_nonneg(s.subrange(1, s.len() as int), v);
        } else {
            assert(s.subrange(1, s.len() as int)[k - 1] == s[k]);
            Self::count_contains(s.subrange(1, s.len() as int), v, k - 1);
        }
    }

    pub fn generate_test_case(
        arr2: Vec<i32>,
        extra: Vec<i32>,
        mutation_kind: u8,
    ) -> (result: (Vec<i32>, Vec<i32>))
        requires
            1 <= arr2.len() <= 1000,
            forall|i: int| 0 <= i < arr2.len() ==> 0 <= #[trigger] arr2[i] <= 1000,
            forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] != arr2[j],
            forall|i: int| 0 <= i < extra.len() ==> 0 <= #[trigger] extra[i] <= 1000,
            1 <= arr2.len() as int + extra.len() as int <= 1000,
        ensures
            1 <= result.0@.len() <= 1000,
            1 <= result.1@.len() <= 1000,
            forall|i: int| 0 <= i < result.0@.len() ==> 0 <= #[trigger] result.0@[i] <= 1000,
            forall|i: int| 0 <= i < result.1@.len() ==> 0 <= #[trigger] result.1@[i] <= 1000,
            forall|i: int, j: int| 0 <= i < j < result.1@.len() ==> result.1@[i] != result.1@[j],
            forall|i: int| 0 <= i < result.1@.len() ==>
                Self::count(result.0@, result.1@[i]) >= 1,
    {
        let mut arr1: Vec<i32> = Vec::new();

        // Copy arr2 elements into arr1
        let mut i: usize = 0;
        while i < arr2.len()
            invariant
                i <= arr2.len(),
                arr1.len() == i,
                1 <= arr2.len() <= 1000,
                forall|k: int| 0 <= k < arr2.len() ==> 0 <= #[trigger] arr2[k] <= 1000,
                forall|k: int| 0 <= k < i as int ==> arr1[k] == arr2[k],
                forall|k: int| 0 <= k < arr1.len() ==> 0 <= #[trigger] arr1[k] <= 1000,
            decreases arr2.len() - i,
        {
            assert(0 <= arr2[i as int] <= 1000);
            arr1.push(arr2[i]);
            i += 1;
        }

        if mutation_kind != 1 {
            // Append extra elements
            let mut j: usize = 0;
            while j < extra.len()
                invariant
                    j <= extra.len(),
                    arr1.len() == arr2.len() + j,
                    arr1.len() <= 1000,
                    1 <= arr2.len() as int + extra.len() as int <= 1000,
                    forall|k: int| 0 <= k < extra.len() ==> 0 <= #[trigger] extra[k] <= 1000,
                    forall|k: int| 0 <= k < arr2.len() ==> arr1[k] == arr2[k],
                    forall|k: int| 0 <= k < arr1.len() ==> 0 <= #[trigger] arr1[k] <= 1000,
                decreases extra.len() - j,
            {
                assert(0 <= extra[j as int] <= 1000);
                arr1.push(extra[j]);
                j += 1;
            }
        }
        // mutation_kind == 1: arr1 = arr2 only (no extra)

        proof {
            let a1 = arr1@;
            let a2 = arr2@;
            assert forall|idx: int| 0 <= idx < a2.len()
                implies Self::count(a1, a2[idx]) >= 1 by {
                assert(a1[idx] == a2[idx]);
                Self::count_contains(a1, a2[idx], idx);
            };
        }

        (arr1, arr2)
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

include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_distinct_arr2(rng: &mut Rng, len: usize) -> Vec<i32> {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    let mut arr = Vec::with_capacity(len);
    while arr.len() < len {
        let v = rng.gen_range_i64(0, 1000) as i32;
        if set.insert(v) {
            arr.push(v);
        }
    }
    arr
}

fn random_extra(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1122);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |arr1: Vec<i32>, arr2: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    n: &mut usize| {
        if *n >= count {
            return;
        }
        let key = format!("{:?}|{:?}", arr1, arr2);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::relative_sort_array(arr1.clone(), arr2.clone());
        writeln!(out, "{}", json!({
            "input": {"arr1": arr1, "arr2": arr2},
            "output": result
        })).unwrap();
        *n += 1;
    };

    // Example 1 from description
    {
        let arr1 = vec![2,3,1,3,2,4,6,7,9,2,19];
        let arr2 = vec![2,1,4,3,9,6];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Example 2 from description
    {
        let arr1 = vec![28,6,22,8,44,17];
        let arr2 = vec![22,28,8,6];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Edge case: single element arrays
    {
        let arr1 = vec![0];
        let arr2 = vec![0];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }
    {
        let arr1 = vec![1000];
        let arr2 = vec![1000];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Edge case: arr2 covers all of arr1
    {
        let arr1 = vec![5, 3, 1];
        let arr2 = vec![3, 1, 5];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Edge case: all same element
    {
        let arr1 = vec![7, 7, 7, 7];
        let arr2 = vec![7];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Edge case: arr1 has elements not in arr2
    {
        let arr1 = vec![10, 20, 30, 40, 50];
        let arr2 = vec![30];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    // Edge case: boundary values
    {
        let arr1 = vec![0, 1000, 500, 0, 1000];
        let arr2 = vec![1000, 0];
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    // Generate diverse random test cases
    while n < count {
        // Size classes for arr2
        let arr2_len: usize = match n % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(200, 500),   // very large
        };
        let arr2_len = arr2_len.min(1000);
        let arr2 = random_distinct_arr2(&mut rng, arr2_len);

        // Extra elements: 0 to (1000 - arr2_len)
        let max_extra = 1000 - arr2_len;
        let extra_len = if max_extra == 0 {
            0
        } else {
            match n % 4 {
                0 => 0,                                              // no extra
                1 => rng.gen_range_usize(1, max_extra.min(10)),      // few extra
                2 => rng.gen_range_usize(1, max_extra.min(100)),     // some extra
                _ => rng.gen_range_usize(1, max_extra),              // many extra
            }
        };
        let extra = random_extra(&mut rng, extra_len);

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (arr1, arr2) = Solution::generate_test_case(arr2, extra, mk);
        emit(arr1, arr2, &mut seen, &mut out, &mut n);
    }
}
