use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: i32) -> (result: i32)
    ensures 1 <= result <= 1000000000, has_no_zero_digits(result as nat),
{
    let mut seed = if raw < 1 { 1 } else if raw > 999999999 { 999999999 } else { raw };
    let mut digits: Vec<i32> = Vec::new();
    proof { lemma_pow10_bound9(); }
    while seed > 0
        invariant 0 <= seed <= 999999999, digits.len() <= 9,
            seed > 0 ==> digits.len() < 9,
            (seed as nat) < pow10((9 - digits.len()) as nat),
            forall|j: int| 0 <= j < digits.len() ==> 1 <= #[trigger] digits[j] <= 9,
        decreases seed,
    {
        proof { lemma_pow10_bound9(); }
        let d = seed % 10;
        digits.push(if d == 0 { 1 } else { d });
        seed = seed / 10;
        proof { if digits.len() == 9 { reveal_with_fuel(pow10, 2); } }
    }
    let mut num: i64 = 0;
    let mut k = 0usize;
    while k < digits.len()
        invariant k <= digits.len() <= 9,
            forall|j: int| 0 <= j < digits.len() ==> 1 <= #[trigger] digits[j] <= 9,
            0 <= num, (num as nat) < pow10(k as nat),
            k > 0 ==> num > 0, has_no_zero_digits(num as nat),
        decreases digits.len() - k,
    {
        let digit = digits[digits.len() - 1 - k] as i64;
        proof {
            lemma_build_bound(num as nat, digit as nat, k as nat);
            lemma_pow10_monotone(k as nat, 9);
            lemma_pow10_bound9();
            lemma_digit_append(num as nat, digit as nat);
        }
        num = num * 10 + digit;
        k += 1;
    }
    proof { lemma_pow10_monotone(digits.len() as nat, 9); lemma_pow10_bound9(); }
    if num == 0 { 1 } else { num as i32 }
}


// Copied from spec.rs (standalone version, without Self:: prefix)
pub open spec fn has_no_zero_digits(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        n % 10 != 0 && has_no_zero_digits(n / 10)
    }
}

// Power-of-10 helper for tracking numeric bounds
pub open spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 }
    else { 10 * pow10((k - 1) as nat) }
}

proof fn lemma_pow10_positive(k: nat)
    ensures pow10(k) >= 1,
    decreases k,
{
    if k > 0 { lemma_pow10_positive((k - 1) as nat); }
}

proof fn lemma_pow10_bound9()
    ensures pow10(9) == 1_000_000_000,
{
    reveal_with_fuel(pow10, 11);
}

proof fn lemma_pow10_monotone(a: nat, b: nat)
    requires a <= b,
    ensures pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_monotone(a, (b - 1) as nat);
        lemma_pow10_positive((b - 1) as nat);
    }
}

// Appending a non-zero digit preserves has_no_zero_digits
proof fn lemma_digit_append(prev: nat, d: nat)
    requires
        has_no_zero_digits(prev),
        1 <= d <= 9,
    ensures
        has_no_zero_digits(prev * 10 + d),
{
    assert((prev * 10 + d) % 10 == d) by (nonlinear_arith)
        requires 1 <= d <= 9, prev >= 0,
    ;
    assert((prev * 10 + d) / 10 == prev) by (nonlinear_arith)
        requires 0 <= d <= 9, prev >= 0,
    ;
}

// Upper-bound step: if num < pow10(k) and digit <= 9 then num*10+digit < pow10(k+1)
proof fn lemma_build_bound(num: nat, digit: nat, k: nat)
    requires
        num < pow10(k),
        digit <= 9,
    ensures
        num * 10 + digit < pow10(k + 1),
{
    lemma_pow10_positive(k);
    assert(num * 10 + digit < 10 * pow10(k)) by (nonlinear_arith)
        requires num < pow10(k), digit <= 9, pow10(k) >= 1,
    ;
}

/// Constructs a valid `num` from a vector of non-zero digits,
/// optionally mutating the digit array first.
///
/// mutation_kind selects the digit-level mutation:
///   0 — identity
///   1 — set all digits to 9
///   2 — set all digits to 1
///   3 — set first digit to 1
///   4 — set last digit to 9
///   5 — nudge first digit up (if < 9)
///   6 — nudge last digit down (if > 1)
pub fn generate_candidate(digits: Vec<u8>, mutation_kind: u8) -> (result: i32)
    requires
        1 <= digits.len() <= 9,
        forall|i: int| 0 <= i < digits.len() ==> 1 <= #[trigger] digits[i] <= 9,
    ensures
        1 <= result <= 1_000_000_000,
        has_no_zero_digits(result as nat),
{
    let mut d = digits;

    // --- Digit-level mutations (each preserves the 1..=9 invariant) ---

    if mutation_kind == 1 {
        // Set all digits to 9
        let mut i: usize = 0;
        while i < d.len()
            invariant
                i <= d.len(),
                d.len() == digits.len(),
                1 <= d.len() <= 9,
                forall|j: int| 0 <= j < d.len() as int ==> 1 <= #[trigger] d[j] <= 9,
            decreases d.len() - i,
        {
            d.set(i, 9u8);
            i += 1;
        }
    } else if mutation_kind == 2 {
        // Set all digits to 1
        let mut i: usize = 0;
        while i < d.len()
            invariant
                i <= d.len(),
                d.len() == digits.len(),
                1 <= d.len() <= 9,
                forall|j: int| 0 <= j < d.len() as int ==> 1 <= #[trigger] d[j] <= 9,
            decreases d.len() - i,
        {
            d.set(i, 1u8);
            i += 1;
        }
    } else if mutation_kind == 3 {
        // Set first digit to 1
        d.set(0, 1u8);
    } else if mutation_kind == 4 {
        // Set last digit to 9
        let last = d.len() - 1;
        d.set(last, 9u8);
    } else if mutation_kind == 5 && d[0] < 9 {
        // Nudge first digit up
        d.set(0, (d[0] + 1) as u8);
    } else if mutation_kind == 6 {
        // Nudge last digit down
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, (d[last] - 1) as u8);
        }
    }
    // else: identity (mutation_kind == 0 or fallback)

    // --- Build number from (possibly mutated) digits ---

    let mut num: i64 = 0;
    let mut k: usize = 0;

    while k < d.len()
        invariant
            0 <= k <= d.len(),
            1 <= d.len() <= 9,
            forall|i: int| 0 <= i < d.len() as int ==> 1 <= #[trigger] d[i] <= 9,
            num >= 0,
            (num as nat) < pow10(k as nat),
            k > 0 ==> num >= 1,
            has_no_zero_digits(num as nat),
        decreases d.len() - k,
    {
        let digit = d[k] as i64;

        proof {
            // 1. Bound: num*10+digit < pow10(k+1)
            lemma_build_bound(num as nat, digit as nat, k as nat);

            // 2. i64 safety: pow10(k) <= pow10(9) = 1_000_000_000
            lemma_pow10_monotone(k as nat, 9);
            lemma_pow10_bound9();

            // 3. has_no_zero_digits preserved
            lemma_digit_append(num as nat, digit as nat);
        }

        num = num * 10 + digit;
        k += 1;
    }

    proof {
        lemma_pow10_monotone(d.len() as nat, 9);
        lemma_pow10_bound9();
    }

    num as i32
}

} // verus!

// ---------------------------------------------------------------------------
// Unverified harness — PRNG, code inclusion, JSONL output
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn mutate(digits: Vec<u8>, mutation_kind: u8) -> i32 {
    generate_candidate(digits, mutation_kind)
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

    // Helper: emit one test case if not yet seen
    let mut emit = |num: i32, seen: &mut HashSet<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let num = generate_test_case(num);
        if *count >= goal || !seen.insert(num) { return; }
        let output = Solution::count_digits(num);
        writeln!(out, "{}", json!({"input": {"num": num}, "output": output})).unwrap();
        *count += 1;
    };

    // --- Example inputs from description.md ---
    emit(mutate(vec![7], 0), &mut seen, &mut out, &mut count);           // 7
    emit(mutate(vec![1, 2, 1], 0), &mut seen, &mut out, &mut count);     // 121
    emit(mutate(vec![1, 2, 4, 8], 0), &mut seen, &mut out, &mut count);  // 1248

    // --- Interesting seed values × all mutations ---
    let seeds: Vec<Vec<u8>> = vec![
        vec![1],
        vec![9],
        vec![1, 1],
        vec![5, 5, 5],
        vec![2, 4, 8],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![9, 9, 9, 9, 9, 9, 9, 9, 9],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9],
        vec![9, 8, 7, 6, 5, 4, 3, 2, 1],
        vec![3, 6, 9],
        vec![1, 5],
    ];

    for s in &seeds {
        for mk in 0..=6u8 {
            if count >= goal { break; }
            let num = mutate(s.clone(), mk);
            emit(num, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // --- Random generation with diverse size classes ---
    let mut _attempts_0 = 0usize;
    while count < goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let num_digits = match count % 5 {
            0 => rng.gen_range_usize(1, 1),   // single digit
            1 => rng.gen_range_usize(1, 3),   // small
            2 => rng.gen_range_usize(3, 5),   // medium
            3 => rng.gen_range_usize(5, 7),   // large
            _ => rng.gen_range_usize(7, 9),   // max
        };

        let mut digits = Vec::with_capacity(num_digits);
        for _ in 0..num_digits {
            // ~20% boundary values, ~80% random
            let d = if rng.gen_u8() % 5 == 0 {
                *[1u8, 9, 5, 1, 9].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_usize(1, 9) as u8
            };
            digits.push(d);
        }

        let mk = rng.gen_u8() % 7;
        let num = mutate(digits, mk);
        emit(num, &mut seen, &mut out, &mut count);
    }
}
