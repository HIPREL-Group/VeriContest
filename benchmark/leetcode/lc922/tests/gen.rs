use vstd::prelude::*;

verus! {

// Copied from spec.rs — only the helper referenced in the requires clause.
pub open spec fn filter_even(s: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else if s[n - 1] % 2 == 0 {
        filter_even(s, n - 1).push(s[n - 1])
    } else {
        filter_even(s, n - 1)
    }
}

// Lemma: filter_even on a prefix is unaffected by appending an element beyond the prefix.
proof fn filter_even_append_irrelevant(s: Seq<i32>, v: i32, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        filter_even(s.push(v), n) == filter_even(s, n),
    decreases n,
{
    if n > 0 {
        assert(s.push(v)[n - 1] == s[n - 1]);
        filter_even_append_irrelevant(s, v, n - 1);
    }
}

// Lemma: appending an even value grows filter_even by one element.
proof fn filter_even_push_even(s: Seq<i32>, v: i32)
    requires
        v % 2 == 0,
    ensures
        filter_even(s.push(v), s.len() as int + 1)
            == filter_even(s, s.len() as int).push(v),
{
    let n = s.len() as int;
    assert(s.push(v)[n] == v);
    filter_even_append_irrelevant(s, v, n);
}

// Lemma: appending an odd value leaves filter_even unchanged.
proof fn filter_even_push_odd(s: Seq<i32>, v: i32)
    requires
        v % 2 != 0,
    ensures
        filter_even(s.push(v), s.len() as int + 1)
            == filter_even(s, s.len() as int),
{
    let n = s.len() as int;
    assert(s.push(v)[n] == v);
    filter_even_append_irrelevant(s, v, n);
}

pub fn generate_test_case(
    evens: Vec<i32>,
    odds: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= evens.len() <= 10000,
        evens.len() == odds.len(),
        forall|i: int| 0 <= i < evens.len()
            ==> 0 <= #[trigger] evens[i] <= 1000 && evens[i] % 2 == 0,
        forall|i: int| 0 <= i < odds.len()
            ==> 0 <= #[trigger] odds[i] <= 1000 && odds[i] % 2 != 0,
    ensures
        2 <= result.len() <= 20000,
        result.len() % 2 == 0,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
        filter_even(result@, result.len() as int).len() == result.len() as int / 2,
{
    // --- apply mutations on construction parameters -------------------------
    let mut ev = evens;
    let mut od = odds;

    if mutation_kind == 1 {
        // Set first even to 0
        ev.set(0, 0);
    } else if mutation_kind == 2 {
        // Set first odd to 1
        od.set(0, 1);
    } else if mutation_kind == 3 {
        // Set first even to 1000
        ev.set(0, 1000);
    } else if mutation_kind == 4 {
        // Set first odd to 999
        od.set(0, 999);
    } else if mutation_kind == 5 {
        // Set first even to boundary 0 and first odd to boundary 1
        ev.set(0, 0);
        od.set(0, 1);
    } else if mutation_kind == 6 {
        // Set last even to 0
        let last = ev.len() - 1;
        ev.set(last, 0);
    } else if mutation_kind == 7 {
        // Set last odd to 1
        let last = od.len() - 1;
        od.set(last, 1);
    }
    // else mutation_kind == 0 or anything else: identity

    // --- interleave evens and odds ------------------------------------------
    let n = ev.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == ev.len(),
            n == od.len(),
            1 <= n <= 10000,
            result.len() == 2 * i,
            forall|j: int| 0 <= j < ev.len()
                ==> 0 <= #[trigger] ev[j] <= 1000 && ev[j] % 2 == 0,
            forall|j: int| 0 <= j < od.len()
                ==> 0 <= #[trigger] od[j] <= 1000 && od[j] % 2 != 0,
            forall|j: int| 0 <= j < result.len()
                ==> 0 <= #[trigger] result[j] <= 1000,
            filter_even(result@, result.len() as int).len() == i as int,
        decreases n - i,
    {
        let e = ev[i];
        let o = od[i];

        let ghost old_seq = result@;
        result.push(e);

        proof {
            filter_even_push_even(old_seq, e);
            assert(result@ == old_seq.push(e));
            assert(filter_even(result@, result.len() as int).len() == i as int + 1);
        }

        let ghost mid_seq = result@;
        result.push(o);

        proof {
            filter_even_push_odd(mid_seq, o);
            assert(result@ == mid_seq.push(o));
            assert(filter_even(result@, result.len() as int).len() == i as int + 1);
        }

        i += 1;
    }

    result
}

} // verus!

// ---------------------------------------------------------------------------
// main() — unverified harness that samples, runs the solution, and emits JSONL
// ---------------------------------------------------------------------------

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

fn random_even(rng: &mut Rng) -> i32 {
    // even values in [0, 1000]: 0, 2, 4, ..., 1000
    (rng.gen_range_i64(0, 500) * 2) as i32
}

fn random_odd(rng: &mut Rng) -> i32 {
    // odd values in [0, 1000]: 1, 3, 5, ..., 999
    (rng.gen_range_i64(0, 499) * 2 + 1) as i32
}

fn make_evens(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| random_even(rng)).collect()
}

fn make_odds(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| random_odd(rng)).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(922);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

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
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sort_array_by_parity_ii(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // --- Example inputs from description.md ---------------------------------
    let example1 = generate_test_case(vec![4, 2], vec![5, 7], 0);
    emit(example1, &mut seen, &mut out, &mut count);

    let example2 = generate_test_case(vec![2], vec![3], 0);
    emit(example2, &mut seen, &mut out, &mut count);

    // --- Structured seeds × all mutation kinds ------------------------------
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    let structured_half_sizes: Vec<usize> = vec![1, 2, 3, 5, 10];

    for &half in &structured_half_sizes {
        let evens: Vec<i32> = (0..half).map(|k| ((k % 501) * 2) as i32).collect();
        let odds: Vec<i32> = (0..half).map(|k| ((k % 500) * 2 + 1) as i32).collect();
        for &mk in &mutation_kinds {
            let nums = generate_test_case(evens.clone(), odds.clone(), mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // --- Size-class sweep with random mutations -----------------------------
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),        // tiny
        (4, 10),       // small
        (11, 100),     // medium
        (101, 500),    // large
        (501, 2000),   // big
        (2001, 10000), // max
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..8 {
            let half = rng.gen_range_usize(*lo, *hi);
            let evens = make_evens(&mut rng, half);
            let odds = make_odds(&mut rng, half);
            let mk = rng.gen_range_usize(0, 7) as u8;
            let nums = generate_test_case(evens, odds, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }

    // --- Fill remaining with random inputs ----------------------------------
    while count < target {
        let half = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let evens = make_evens(&mut rng, half);
        let odds = make_odds(&mut rng, half);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let nums = generate_test_case(evens, odds, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
