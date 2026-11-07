use vstd::prelude::*;

verus! {

pub open spec fn count_value(nums: Seq<i32>, end: int, value: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value(nums, end - 1, value)
            + if nums[end - 1] as int == value { 1int } else { 0int }
    }
}

proof fn lemma_count_prefix(s1: Seq<i32>, s2: Seq<i32>, end: int, v: int)
    requires
        0 <= end <= s1.len(),
        0 <= end <= s2.len(),
        forall |i: int| 0 <= i < end ==> s1[i] == s2[i],
    ensures
        count_value(s1, end, v) == count_value(s2, end, v),
    decreases end,
{
    if end > 0 {
        lemma_count_prefix(s1, s2, end - 1, v);
    }
}

proof fn lemma_count_mono(nums: Seq<i32>, e1: int, e2: int, v: int)
    requires
        0 <= e1 <= e2 <= nums.len(),
    ensures
        count_value(nums, e1, v) <= count_value(nums, e2, v),
    decreases e2 - e1,
{
    if e1 < e2 {
        lemma_count_mono(nums, e1, e2 - 1, v);
    }
}

proof fn lemma_count_nonneg(nums: Seq<i32>, end: int, v: int)
    requires
        0 <= end <= nums.len(),
    ensures
        count_value(nums, end, v) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_count_nonneg(nums, end - 1, v);
    }
}

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        forall |v: int| 1 <= v <= 50 ==> 0 <= #[trigger] count_value(nums@, nums.len() as int, v) <= 2,
    ensures
        1 <= result.len() <= 50,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 50,
        forall |v: int| 1 <= v <= 50 ==> 0 <= #[trigger] count_value(result@, result.len() as int, v) <= 2,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() > 1 {
        // shrink: remove last element
        let ghost old_seq = nums@;
        let ghost old_len = nums@.len();
        let mut d = nums;
        d.pop();
        proof {
            assert(d@.len() == old_len - 1);
            assert(d@.len() >= 1);
            assert(old_len >= 2);
            assert(d@.len() <= old_seq.len());
            assert forall |i: int| 0 <= i < d@.len() implies d@[i] == old_seq[i] by {};
            assert forall |i: int| 0 <= i < d@.len() implies 1 <= #[trigger] d@[i] <= 50 by {
                assert(d@[i] == old_seq[i]);
            };
            assert forall |v: int| 1 <= v <= 50 implies
                0 <= #[trigger] count_value(d@, d@.len() as int, v) <= 2
            by {
                lemma_count_nonneg(d@, d@.len() as int, v);
                lemma_count_prefix(d@, old_seq, d@.len() as int, v);
                lemma_count_mono(old_seq, d@.len() as int, old_seq.len() as int, v);
            };
        }
        d
    } else if mutation_kind == 2 {
        // extract single element from first position
        let val = nums[0];
        let mut r: Vec<i32> = Vec::new();
        r.push(val);
        proof {
            assert forall |v: int| 1 <= v <= 50 implies
                0 <= #[trigger] count_value(r@, r@.len() as int, v) <= 2
            by {
                assert(count_value(r@, 1, v) ==
                    count_value(r@, 0, v)
                    + if r@[0] as int == v { 1int } else { 0int });
            };
        }
        r
    } else if mutation_kind == 3 {
        // duplicate first element into a pair
        let val = nums[0];
        let mut r: Vec<i32> = Vec::new();
        r.push(val);
        r.push(val);
        proof {
            assert forall |v: int| 1 <= v <= 50 implies
                0 <= #[trigger] count_value(r@, r@.len() as int, v) <= 2
            by {
                assert(count_value(r@, 2, v) ==
                    count_value(r@, 1, v)
                    + if r@[1] as int == v { 1int } else { 0int });
                assert(count_value(r@, 1, v) ==
                    count_value(r@, 0, v)
                    + if r@[0] as int == v { 1int } else { 0int });
            };
        }
        r
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // extract pair from first two positions (distinct or equal)
        let a = nums[0];
        let b = nums[1];
        let mut r: Vec<i32> = Vec::new();
        r.push(a);
        r.push(b);
        proof {
            assert forall |v: int| 1 <= v <= 50 implies
                0 <= #[trigger] count_value(r@, r@.len() as int, v) <= 2
            by {
                assert(count_value(r@, 2, v) ==
                    count_value(r@, 1, v)
                    + if r@[1] as int == v { 1int } else { 0int });
                assert(count_value(r@, 1, v) ==
                    count_value(r@, 0, v)
                    + if r@[0] as int == v { 1int } else { 0int });
            };
        }
        r
    } else if mutation_kind == 5 && nums.len() > 2 {
        // shrink by 2: remove last two elements
        let ghost old_seq = nums@;
        let ghost old_len = nums@.len();
        let mut d = nums;
        d.pop();
        let ghost mid_seq = d@;
        let ghost mid_len = d@.len();
        d.pop();
        proof {
            assert(mid_len == old_len - 1);
            assert(d@.len() == mid_len - 1);
            assert(d@.len() == old_len - 2);
            assert(d@.len() >= 1);
            assert forall |i: int| 0 <= i < mid_len implies mid_seq[i] == old_seq[i] by {};
            assert forall |i: int| 0 <= i < d@.len() implies d@[i] == mid_seq[i] by {};
            assert forall |i: int| 0 <= i < d@.len() implies d@[i] == old_seq[i] by {
                assert(d@[i] == mid_seq[i]);
                assert(mid_seq[i] == old_seq[i]);
            };
            assert forall |i: int| 0 <= i < d@.len() implies 1 <= #[trigger] d@[i] <= 50 by {
                assert(d@[i] == old_seq[i]);
            };
            assert forall |v: int| 1 <= v <= 50 implies
                0 <= #[trigger] count_value(d@, d@.len() as int, v) <= 2
            by {
                lemma_count_nonneg(d@, d@.len() as int, v);
                lemma_count_prefix(d@, old_seq, d@.len() as int, v);
                lemma_count_mono(old_seq, d@.len() as int, old_seq.len() as int, v);
            };
        }
        d
    } else {
        // fallback: identity
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn make_valid_nums(rng: &mut Rng, target_len: usize) -> Vec<i32> {
    let mut nums = Vec::new();
    let mut count = [0u8; 51];
    while nums.len() < target_len {
        let v = rng.gen_range_i64(1, 50) as i32;
        if count[v as usize] < 2 {
            count[v as usize] += 1;
            nums.push(v);
        }
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3158);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::duplicate_numbers_xor(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 1, 3],
        vec![1, 2, 3],
        vec![1, 2, 2, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut total);
    }

    // Curated seed inputs for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![50],
        vec![1, 1],
        vec![50, 50],
        vec![25, 25],
        vec![1, 2],
        vec![1, 50],
        vec![1, 1, 2, 2],
        vec![49, 50, 49, 50],
        vec![1, 2, 3, 4, 5],
        vec![1, 1, 2, 2, 3, 3, 4, 4, 5, 5],
        vec![10, 20, 30, 40, 50],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
             21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
             41, 42, 43, 44, 45, 46, 47, 48, 49, 50],
        vec![1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10,
             11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20,
             21, 21, 22, 22, 23, 23, 24, 24, 25, 25],
        vec![7],
        vec![42, 42],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with varied sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),    // tiny
        (4, 10),   // small
        (11, 25),  // medium
        (26, 40),  // large
        (41, 50),  // max
    ];

    for _ in 0..80 {
        let (lo, hi) = size_classes[rng.gen_range_usize(0, size_classes.len() - 1)];
        let len = rng.gen_range_usize(lo, hi);
        let nums = make_valid_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 5) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }

    // Fill remaining with random identity-mutated inputs
    while total < count {
        let len = rng.gen_range_usize(1, 50);
        let nums = make_valid_nums(&mut rng, len);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut total);
    }
}
