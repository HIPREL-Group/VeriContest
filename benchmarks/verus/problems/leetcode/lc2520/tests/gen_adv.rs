use vstd::prelude::*;

verus! {


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


pub fn generate_candidate(num: i32) -> (result: i32)
    requires
        1 <= num <= 1_000_000_000,
    ensures
        1 <= result <= 1_000_000_000,
        result == num,
{
    num
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

/// Build a number in [1, 1_000_000_000] with digits in 1..=9 (no zero digits), up to 9 digits.
fn random_num_no_zero(rng: &mut Rng) -> i32 {
    let nd = rng.gen_range_usize(1, 9);
    let mut v: u64 = 0;
    for i in 0..nd {
        let d = if i == 0 {
            rng.gen_range_usize(1, 9) as u64
        } else {
            rng.gen_range_usize(1, 9) as u64
        };
        v = v * 10 + d;
        if v > 1_000_000_000 {
            v = v / 10;
            break;
        }
    }
    if v < 1 {
        v = 1;
    }
    if v > 1_000_000_000 {
        v = 1_000_000_000;
    }
    v as i32
}

fn pick_num(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 7,
        1 => 121,
        2 => 1248,
        3 => 1_000_000_000,
        4 => 1,
        5 => 999_999_999,
        6 => 111_111_111,
        7 => 999_999_991,
        8 => 222222222.min(1_000_000_000),
        9 => random_num_no_zero(rng),
        _ => random_num_no_zero(rng),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let n = pick_num(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 1_000_000_000 { 1_000_000_000 } else { n };
        let out = generate_test_case(n);
        println!("{{\"num\":{}}}", out);
    }
}
