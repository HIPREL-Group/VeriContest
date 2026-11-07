use vstd::prelude::*;

verus! {

/// Build an array of unique digits from a boolean selection mask over digits 1–9.
/// `sel[i]` == true means digit `i+1` is included (in ascending order).
fn build_from_selection(sel: &Vec<bool>) -> (arr: Vec<i32>)
    requires
        sel.len() == 9,
        exists|i: int| 0 <= i < 9 && sel[i] == true,
    ensures
        1 <= arr.len() <= 9,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 9,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < 9
        invariant
            0 <= i <= 9,
            sel.len() == 9,
            arr.len() <= i,
            forall|k: int| 0 <= k < arr.len() ==> 1 <= #[trigger] arr[k] <= 9,
            forall|k: int| 0 <= k < arr.len() ==> arr[k] <= i as i32,
            forall|k: int, l: int| 0 <= k < l < arr.len() as int ==> arr[k] < arr[l],
            forall|k: int, l: int| 0 <= k < l < arr.len() as int ==> arr[k] != arr[l],
            (exists|j: int| 0 <= j < i as int && sel[j] == true) ==> arr.len() >= 1,
        decreases 9 - i,
    {
        if sel[i] {
            let digit = (i + 1) as i32;
            assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] <= i as i32);
            assert(digit == i as i32 + 1);
            arr.push(digit);
        }
        i += 1;
    }
    arr
}

pub fn generate_test_case(
    sel1: Vec<bool>,
    sel2: Vec<bool>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        sel1.len() == 9,
        sel2.len() == 9,
        exists|i: int| 0 <= i < 9 && sel1[i] == true,
        exists|i: int| 0 <= i < 9 && sel2[i] == true,
    ensures
        1 <= result.0.len() <= 9,
        1 <= result.1.len() <= 9,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 9,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 9,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
{
    let mut nums1 = build_from_selection(&sel1);
    let mut nums2 = build_from_selection(&sel2);

    if mutation_kind == 1 && nums1.len() > 1 {
        // shrink nums1 by one
        nums1.pop();
        (nums1, nums2)
    } else if mutation_kind == 2 && nums2.len() > 1 {
        // shrink nums2 by one
        nums2.pop();
        (nums1, nums2)
    } else if mutation_kind == 3 && nums1.len() > 1 {
        // keep only first element of nums1
        let first = nums1[0];
        let mut single: Vec<i32> = Vec::new();
        single.push(first);
        (single, nums2)
    } else if mutation_kind == 4 && nums2.len() > 1 {
        // keep only first element of nums2
        let first = nums2[0];
        let mut single: Vec<i32> = Vec::new();
        single.push(first);
        (nums1, single)
    } else {
        // identity
        (nums1, nums2)
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
    fn gen_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_selection(rng: &mut Rng) -> Vec<bool> {
    loop {
        let sel: Vec<bool> = (0..9).map(|_| rng.gen_bool()).collect();
        if sel.iter().any(|&b| b) {
            return sel;
        }
    }
}

fn selection_from_digits(digits: &[i32]) -> Vec<bool> {
    let mut sel = vec![false; 9];
    for &d in digits {
        sel[(d - 1) as usize] = true;
    }
    sel
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2605);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", nums1, nums2);
        if !seen.insert(key) { return; }
        let result = Solution::min_number(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![4, 1, 3], vec![5, 7]),
        (vec![3, 5, 2, 6], vec![3, 1, 7]),
    ];
    for (n1, n2) in &examples {
        emit(n1.clone(), n2.clone(), &mut seen, &mut out, &mut emitted);
    }

    // Boundary cases: single-element arrays
    for d1 in 1..=9i32 {
        for d2 in 1..=9i32 {
            let s1 = selection_from_digits(&[d1]);
            let s2 = selection_from_digits(&[d2]);
            let (n1, n2) = generate_test_case(s1, s2, 0);
            emit(n1, n2, &mut seen, &mut out, &mut emitted);
        }
    }

    // Full overlap: same selection for both
    for len in 1..=9usize {
        let sel: Vec<bool> = (0..9).map(|i| i < len).collect();
        let (n1, n2) = generate_test_case(sel.clone(), sel.clone(), 0);
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }

    // No overlap: disjoint selections
    let disjoint_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3], vec![4, 5, 6]),
        (vec![1, 3, 5, 7, 9], vec![2, 4, 6, 8]),
        (vec![1], vec![9]),
        (vec![1, 2, 3, 4], vec![5, 6, 7, 8, 9]),
    ];
    for (d1, d2) in &disjoint_pairs {
        let s1 = selection_from_digits(d1);
        let s2 = selection_from_digits(d2);
        let (n1, n2) = generate_test_case(s1, s2, 0);
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }

    // All mutation kinds on varied seeds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];
    for _ in 0..30 {
        let s1 = random_selection(&mut rng);
        let s2 = random_selection(&mut rng);
        for &mk in &mutation_kinds {
            let (n1, n2) = generate_test_case(s1.clone(), s2.clone(), mk);
            emit(n1, n2, &mut seen, &mut out, &mut emitted);
        }
    }

    // Fill remaining with random selections and random mutations
    while emitted < count {
        let s1 = random_selection(&mut rng);
        let s2 = random_selection(&mut rng);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let (n1, n2) = generate_test_case(s1, s2, mk);
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }
}
