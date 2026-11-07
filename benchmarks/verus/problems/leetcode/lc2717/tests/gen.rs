use vstd::prelude::*;

verus! {

pub open spec fn is_perm(nums: Seq<i32>) -> bool {
    let n = nums.len();
    &&& 2 <= n <= 50
    &&& forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= n
    &&& forall |i: int, j: int| 0 <= i < j < n ==> nums[i] != nums[j]
}

pub open spec fn is_pos_1(nums: Seq<i32>, i: int) -> bool {
    0 <= i < nums.len() && nums[i] == 1
}

pub open spec fn is_pos_n(nums: Seq<i32>, i: int) -> bool {
    0 <= i < nums.len() && nums[i] == nums.len() as i32
}

pub open spec fn filler_count(j: int, p1: int, pn: int) -> int
    decreases j,
{
    if j <= 0 { 0 }
    else if (j - 1) == p1 || (j - 1) == pn { filler_count(j - 1, p1, pn) }
    else { filler_count(j - 1, p1, pn) + 1 }
}

proof fn lemma_filler_count_nonneg(j: int, p1: int, pn: int)
    requires 0 <= j,
    ensures filler_count(j, p1, pn) >= 0,
    decreases j,
{
    if j <= 0 {} else { lemma_filler_count_nonneg(j - 1, p1, pn); }
}

proof fn lemma_filler_count_mono(a: int, b: int, p1: int, pn: int)
    requires 0 <= a <= b,
    ensures filler_count(a, p1, pn) <= filler_count(b, p1, pn),
    decreases b - a,
{
    if a < b { lemma_filler_count_mono(a, b - 1, p1, pn); }
}

proof fn lemma_filler_count_strict(i: int, j: int, p1: int, pn: int)
    requires 0 <= i < j, i != p1, i != pn,
    ensures filler_count(i, p1, pn) < filler_count(j, p1, pn),
{
    lemma_filler_count_mono(i + 1, j, p1, pn);
}

proof fn lemma_filler_count_eq(j: int, p1: int, pn: int)
    requires 0 <= j, p1 >= 0, pn >= 0, p1 != pn,
    ensures filler_count(j, p1, pn) == j
        - (if p1 < j { 1int } else { 0int })
        - (if pn < j { 1int } else { 0int }),
    decreases j,
{
    if j > 0 { lemma_filler_count_eq(j - 1, p1, pn); }
}

pub fn generate_test_case(
    n: u8, pos1: u8, posn: u8, mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= n <= 50,
        pos1 < n,
        posn < n,
        pos1 != posn,
    ensures
        is_perm(result@),
        exists |i: int| is_pos_1(result@, i),
        exists |i: int| is_pos_n(result@, i),
{
    let nn = n as usize;
    let p1 = pos1 as usize;
    let pn = posn as usize;
    let mut v: Vec<i32> = Vec::new();
    let mut fv: i32 = 2;
    let mut j: usize = 0;

    proof { lemma_filler_count_eq(nn as int, p1 as int, pn as int); }

    while j < nn
        invariant
            nn == n as usize, 2 <= n <= 50,
            p1 == pos1 as usize, pn == posn as usize,
            pos1 < n, posn < n, pos1 != posn,
            0 <= j <= nn, v.len() == j,
            fv as int == 2 + filler_count(j as int, p1 as int, pn as int),
            filler_count(nn as int, p1 as int, pn as int) == nn as int - 2,
            j > p1 ==> v@[p1 as int] == 1i32,
            j > pn ==> v@[pn as int] == n as i32,
            forall |k: int| 0 <= k < j as int && k != p1 as int && k != pn as int
                ==> (#[trigger] v@[k]) as int == 2 + filler_count(k, p1 as int, pn as int),
            forall |k: int| 0 <= k < j as int
                ==> 1 <= #[trigger] v@[k] <= n as i32,
        decreases nn - j,
    {
        if j == p1 {
            v.push(1i32);
        } else if j == pn {
            v.push(n as i32);
        } else {
            proof {
                lemma_filler_count_nonneg(j as int, p1 as int, pn as int);
                lemma_filler_count_mono(j as int, nn as int, p1 as int, pn as int);
            }
            v.push(fv);
            fv = fv + 1;
        }
        j = j + 1;
    }

    if mutation_kind == 1u8 {
        v.set(p1, n as i32);
        v.set(pn, 1i32);
    }

    proof {
        // Existence
        if mutation_kind == 1u8 {
            assert(is_pos_1(v@, pn as int));
            assert(is_pos_n(v@, p1 as int));
        } else {
            assert(is_pos_1(v@, p1 as int));
            assert(is_pos_n(v@, pn as int));
        }

        // Values in range [1, n]
        assert forall |k: int| 0 <= k < v@.len()
            implies 1 <= #[trigger] v@[k] <= n as i32
        by {
            if k == p1 as int || k == pn as int {
            } else {
                lemma_filler_count_nonneg(k, p1 as int, pn as int);
                lemma_filler_count_mono(k + 1, nn as int, p1 as int, pn as int);
                assert(v@[k] as int == 2 + filler_count(k, p1 as int, pn as int));
                assert(filler_count(k, p1 as int, pn as int) >= 0);
                assert(filler_count(k, p1 as int, pn as int) <= nn as int - 3);
            }
        }

        // Uniqueness
        assert forall |a: int, b: int| 0 <= a < b < v@.len()
            implies v@[a] != v@[b]
        by {
            if (a == p1 as int || a == pn as int) && (b == p1 as int || b == pn as int) {
                // Both special: values are 1 and n (or n and 1), n >= 2
            } else if a == p1 as int || a == pn as int {
                // a is special, b is filler
                lemma_filler_count_nonneg(b, p1 as int, pn as int);
                lemma_filler_count_mono(b + 1, nn as int, p1 as int, pn as int);
                assert(v@[b] as int == 2 + filler_count(b, p1 as int, pn as int));
                assert(filler_count(b, p1 as int, pn as int) >= 0);
                assert(filler_count(b, p1 as int, pn as int) <= nn as int - 3);
                // v@[b] in [2, n-1], special is 1 or n
            } else if b == p1 as int || b == pn as int {
                // b is special, a is filler
                lemma_filler_count_nonneg(a, p1 as int, pn as int);
                lemma_filler_count_mono(a + 1, nn as int, p1 as int, pn as int);
                assert(v@[a] as int == 2 + filler_count(a, p1 as int, pn as int));
                assert(filler_count(a, p1 as int, pn as int) >= 0);
                assert(filler_count(a, p1 as int, pn as int) <= nn as int - 3);
            } else {
                // Both fillers: distinct by filler_count strict monotonicity
                lemma_filler_count_strict(a, b, p1 as int, pn as int);
                assert(v@[a] as int == 2 + filler_count(a, p1 as int, pn as int));
                assert(v@[b] as int == 2 + filler_count(b, p1 as int, pn as int));
            }
        }
    }

    v
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

extern crate serde_json;
use serde_json::json;

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2717);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::semi_ordered_permutation(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    for ex in [
        vec![2, 1, 4, 3],
        vec![2, 4, 1, 3],
        vec![1, 3, 4, 2, 5],
    ] {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Boundary: already semi-ordered [1, ..., n]
    for n in [2usize, 3, 5, 10, 50] {
        emit((1..=n as i32).collect(), &mut seen, &mut out, &mut emitted);
    }

    // Reversed: [n, n-1, ..., 1]
    for n in [2usize, 3, 5, 10, 50] {
        emit((1..=n as i32).rev().collect(), &mut seen, &mut out, &mut emitted);
    }

    // Construct via generate_test_case with diverse parameters
    let sizes: Vec<u8> = vec![2, 3, 4, 5, 8, 10, 15, 20, 30, 40, 50];
    for &sz in &sizes {
        for (pos1, posn) in [
            (0, sz - 1), (sz - 1, 0), (0, 1),
            (sz - 2, sz - 1), (sz / 2, 0), (0, sz / 2),
        ] {
            if pos1 >= sz || posn >= sz || pos1 == posn { continue; }
            for mk in 0..2u8 {
                let result = generate_test_case(sz, pos1, posn, mk);
                emit(result, &mut seen, &mut out, &mut emitted);
            }
        }
    }

    // Random permutations via Fisher-Yates
    while emitted < count {
        let n = rng.gen_range_usize(2, 50);
        let perm = random_perm(&mut rng, n);
        emit(perm, &mut seen, &mut out, &mut emitted);
    }
}
