use vstd::prelude::*;

verus! {

// Copied from spec.rs as standalone spec fn (consistency checker strips Self::)
pub open spec fn filter_positive(s: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else if s[n - 1] > 0 {
        filter_positive(s, n - 1).push(s[n - 1])
    } else {
        filter_positive(s, n - 1)
    }
}

// filter_positive on an all-positive prefix has length == n
proof fn lemma_filter_pos_prefix(s: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
        forall |i: int| 0 <= i < n ==> s[i] > 0i32,
    ensures
        filter_positive(s, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_filter_pos_prefix(s, n - 1);
    }
}

// Negative elements don't change filter_positive length
proof fn lemma_filter_neg_suffix(s: Seq<i32>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= s.len(),
        forall |i: int| lo <= i < hi ==> s[i] < 0i32,
    ensures
        filter_positive(s, hi).len() == filter_positive(s, lo).len(),
    decreases hi - lo,
{
    if hi > lo {
        lemma_filter_neg_suffix(s, lo, hi - 1);
    }
}

pub fn generate_test_case(
    pos: Vec<i32>,
    neg: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= pos.len() <= 100_000,
        pos.len() == neg.len(),
        forall |i: int| 0 <= i < pos.len() ==> 1 <= #[trigger] pos[i] <= 100_000,
        forall |i: int| 0 <= i < neg.len() ==> -100_000 <= #[trigger] neg[i] <= -1,
    ensures
        2 <= result.len() <= 200_000,
        result.len() % 2 == 0,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i] != 0,
        forall |i: int| 0 <= i < result.len() ==> -100_000 <= #[trigger] result[i] <= 100_000,
        filter_positive(result@, result.len() as int).len() == result.len() as int / 2,
{
    let half = pos.len();
    let mut result: Vec<i32> = Vec::new();

    // Append positive values (with optional value mutation)
    let mut i: usize = 0;
    while i < half
        invariant
            0 <= i <= half,
            half == pos.len(),
            half == neg.len(),
            1 <= half <= 100_000,
            result.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] result[j] <= 100_000,
            forall |j: int| 0 <= j < i as int ==> result[j] > 0i32,
            forall |k: int| 0 <= k < pos.len() ==> 1 <= #[trigger] pos[k] <= 100_000,
        decreases half - i,
    {
        let val = if mutation_kind == 1 {
            1i32                                        // min positive boundary
        } else if mutation_kind == 2 {
            100_000i32                                  // max positive boundary
        } else if mutation_kind == 3 && pos[i] < 100_000 {
            pos[i] + 1                                  // nudge up
        } else if mutation_kind == 4 && pos[i] > 1 {
            pos[i] - 1                                  // nudge down
        } else {
            pos[i]                                      // identity
        };
        result.push(val);
        i += 1;
    }

    // Append negative values (with optional value mutation)
    let mut j: usize = 0;
    while j < half
        invariant
            0 <= j <= half,
            half == pos.len(),
            half == neg.len(),
            1 <= half <= 100_000,
            result.len() == half + j,
            forall |k: int| 0 <= k < half as int ==> 1 <= #[trigger] result[k] <= 100_000,
            forall |k: int| 0 <= k < half as int ==> result[k] > 0i32,
            forall |k: int| half as int <= k < (half + j) as int
                ==> -100_000 <= #[trigger] result[k] <= -1,
            forall |k: int| half as int <= k < (half + j) as int
                ==> result[k] < 0i32,
            forall |m: int| 0 <= m < neg.len() ==> -100_000 <= #[trigger] neg[m] <= -1,
        decreases half - j,
    {
        let val = if mutation_kind == 5 {
            -1i32                                       // max negative boundary
        } else if mutation_kind == 6 {
            -100_000i32                                 // min negative boundary
        } else if mutation_kind == 7 && neg[j] < -1 {
            neg[j] + 1                                  // nudge up
        } else if mutation_kind == 8 && neg[j] > -100_000 {
            neg[j] - 1                                  // nudge down
        } else {
            neg[j]                                      // identity
        };
        result.push(val);
        j += 1;
    }

    proof {
        // result[0..half) are all > 0; result[half..2*half) are all < 0
        lemma_filter_pos_prefix(result@, half as int);
        lemma_filter_neg_suffix(result@, half as int, result.len() as int);
        assert(result.len() == 2 * half);
        assert(result.len() % 2 == 0);
    }

    result
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_pos_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(1, 100_000) as i32).collect()
}

fn random_neg_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(-100_000, -1) as i32).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::rearrange_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![3, 1, -2, -5, 2, -4], &mut seen, &mut out, &mut count);
    emit(vec![-1, 1], &mut seen, &mut out, &mut count);

    // Handcrafted seeds × all mutation kinds
    let mutation_kinds: Vec<u8> = (0..=8).collect();
    let handcrafted: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 1, 1], vec![-1, -1, -1]),
        (vec![100_000, 100_000, 100_000], vec![-100_000, -100_000, -100_000]),
        (vec![1], vec![-1]),
        (vec![1, 100_000], vec![-100_000, -1]),
        (vec![50_000, 1, 100_000, 42], vec![-50_000, -1, -100_000, -42]),
    ];

    for (pos, neg) in &handcrafted {
        for &mk in &mutation_kinds {
            let result = generate_test_case(pos.clone(), neg.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random tests across size classes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 2),       // tiny  (2-4 elements total)
        (2, 5),       // small (4-10 elements)
        (6, 50),      // medium
        (51, 500),    // large
        (501, 5000),  // very large
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..8 {
            if count >= goal { break; }
            let half = rng.gen_range_usize(*lo, *hi);
            let pos = random_pos_vec(&mut rng, half);
            let neg = random_neg_vec(&mut rng, half);
            let mk = rng.gen_range_usize(0, 8) as u8;
            let result = generate_test_case(pos, neg, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random tests
    while count < goal {
        let half = match count % 5 {
            0 => rng.gen_range_usize(1, 2),
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 50),
            3 => rng.gen_range_usize(51, 500),
            _ => rng.gen_range_usize(501, 5000),
        };
        let pos = random_pos_vec(&mut rng, half);
        let neg = random_neg_vec(&mut rng, half);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = generate_test_case(pos, neg, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
