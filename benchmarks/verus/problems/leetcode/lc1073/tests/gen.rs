use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr1: Vec<i32>, arr2: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= arr1.len() <= 1000,
        1 <= arr2.len() <= 1000,
        forall|i: int| 0 <= i < arr1.len() ==> (#[trigger] arr1[i] == 0 || arr1[i] == 1),
        forall|i: int| 0 <= i < arr2.len() ==> (#[trigger] arr2[i] == 0 || arr2[i] == 1),
        arr1.len() == 1 || arr1[0] == 1,
        arr2.len() == 1 || arr2[0] == 1,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1[i] == 0 || result.1[i] == 1),
        result.0.len() == 1 || result.0[0] == 1,
        result.1.len() == 1 || result.1[0] == 1,
{
    if mutation_kind == 0 {
        // identity
        (arr1, arr2)
    } else if mutation_kind == 1 {
        // set last bit of arr1 to 1
        let mut a = arr1;
        let last = a.len() - 1;
        a.set(last, 1);
        (a, arr2)
    } else if mutation_kind == 2 {
        // set last bit of arr1 to 0
        let mut a = arr1;
        let last = a.len() - 1;
        a.set(last, 0);
        (a, arr2)
    } else if mutation_kind == 3 {
        // set last bit of arr2 to 1
        let mut b = arr2;
        let last = b.len() - 1;
        b.set(last, 1);
        (arr1, b)
    } else if mutation_kind == 4 {
        // set last bit of arr2 to 0
        let mut b = arr2;
        let last = b.len() - 1;
        b.set(last, 0);
        (arr1, b)
    } else if mutation_kind == 5 && arr1.len() < 1000 && arr1[0] == 1 {
        // grow arr1 by appending a 0
        let mut a = arr1;
        a.push(0);
        (a, arr2)
    } else if mutation_kind == 6 && arr2.len() < 1000 && arr2[0] == 1 {
        // grow arr2 by appending a 0
        let mut b = arr2;
        b.push(0);
        (arr1, b)
    } else if mutation_kind == 7 && arr1.len() > 1 {
        // shrink arr1 by removing last element
        let mut a = arr1;
        a.pop();
        (a, arr2)
    } else if mutation_kind == 8 && arr2.len() > 1 {
        // shrink arr2 by removing last element
        let mut b = arr2;
        b.pop();
        (arr1, b)
    } else if mutation_kind == 9 {
        // swap arr1 and arr2
        (arr2, arr1)
    } else if mutation_kind == 10 {
        // set all bits of arr1 to 1
        let mut a = arr1;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr1.len(),
                1 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == 1,
                forall|j: int| i <= j < a.len() ==> a[j] == arr1[j],
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        (a, arr2)
    } else if mutation_kind == 11 {
        // set all bits of arr2 to 1
        let mut b = arr2;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == arr2.len(),
                1 <= b.len() <= 1000,
                forall|j: int| 0 <= j < i ==> b[j] == 1,
                forall|j: int| i <= j < b.len() ==> b[j] == arr2[j],
            decreases b.len() - i,
        {
            b.set(i, 1);
            i += 1;
        }
        (arr1, b)
    } else if mutation_kind == 12 {
        // set arr1 to [0] (zero)
        let mut a: Vec<i32> = Vec::new();
        a.push(0);
        (a, arr2)
    } else if mutation_kind == 13 {
        // set arr2 to [0] (zero)
        let mut b: Vec<i32> = Vec::new();
        b.push(0);
        (arr1, b)
    } else if mutation_kind == 14 {
        // both become [0]
        let mut a: Vec<i32> = Vec::new();
        a.push(0);
        let mut b: Vec<i32> = Vec::new();
        b.push(0);
        (a, b)
    } else {
        // fallback: identity
        (arr1, arr2)
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

extern crate serde_json;
use serde_json::json;

fn random_negabinary(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for i in 0..len {
        if i == 0 && len > 1 {
            arr.push(1); // no leading zeros
        } else {
            arr.push(rng.gen_range_usize(0, 1) as i32);
        }
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1073);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a1: Vec<i32>, a2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}|{:?}", a1, a2);
        if !seen.insert(key) { return; }
        let output = Solution::add_negabinary(a1.clone(), a2.clone());
        writeln!(out, "{}", json!({"input": {"arr1": a1, "arr2": a2}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1,1,1,1,1], vec![1,0,1]),
        (vec![0], vec![0]),
        (vec![0], vec![1]),
    ];

    for (a1, a2) in &examples {
        let (r1, r2) = generate_test_case(a1.clone(), a2.clone(), 0);
        emit(r1, r2, &mut seen, &mut out, &mut count);
    }

    // Seed pairs for structured testing
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1,0], vec![1]),
        (vec![1,1], vec![1,1]),
        (vec![1,0,0], vec![1,0,0]),
        (vec![1,0,1,0], vec![1,1,0,1]),
        (vec![1], vec![0]),
        (vec![1,1,1,1,1,1,1,1], vec![1,1,1,1,1,1,1,1]),
        (vec![1,0,0,0,0,0,0,0,0,0], vec![1]),
        (vec![1,0,1,0,1,0,1,0,1,0], vec![1,0,1,0,1,0,1,0,1,0]),
    ];

    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply all mutations to seed pairs
    for (a1, a2) in &seed_pairs {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let (r1, r2) = generate_test_case(a1.clone(), a2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut count);
        }
    }

    // Random pairs with random mutations across size classes
    while count < target {
        let len1 = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let len2 = match (count + 2) % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let a1 = random_negabinary(&mut rng, len1);
        let a2 = random_negabinary(&mut rng, len2);
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (r1, r2) = generate_test_case(a1, a2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut count);
    }
}
