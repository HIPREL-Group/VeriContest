use vstd::prelude::*;

verus! {

pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        seq_sum(s, end - 1) + s[end - 1] as int
    }
}

pub open spec fn seq_min(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        if end <= 0 { 0 } else { s[0] as int }
    } else {
        let prev = seq_min(s, end - 1);
        let cur = s[end - 1] as int;
        if prev <= cur { prev } else { cur }
    }
}

pub open spec fn min_moves_spec(nums: Seq<i32>) -> int {
    let n = nums.len() as int;
    seq_sum(nums, n) - n * seq_min(nums, n)
}

proof fn lemma_seq_sum_constant(s: Seq<i32>, n: int, val: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] as int == val,
    ensures
        seq_sum(s, n) == n * val,
    decreases n,
{
    if n == 0 {
        assert(seq_sum(s, 0) == 0int);
        assert(0int * val == 0int) by (nonlinear_arith);
    } else {
        lemma_seq_sum_constant(s, n - 1, val);
        assert(seq_sum(s, n - 1) == (n - 1) * val);
        assert(s[n - 1] as int == val);
        assert((n - 1) * val + val == n * val) by (nonlinear_arith)
            requires n >= 1;
    }
}

proof fn lemma_seq_min_constant(s: Seq<i32>, n: int, val: int)
    requires
        1 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] as int == val,
    ensures
        seq_min(s, n) == val,
    decreases n,
{
    if n > 1 {
        lemma_seq_min_constant(s, n - 1, val);
    }
}

proof fn lemma_seq_min_ge_base(s: Seq<i32>, n: int, base: int)
    requires
        1 <= n <= s.len(),
        s[0] as int == base,
        forall|i: int| 0 <= i < n ==> s[i] as int >= base,
    ensures
        seq_min(s, n) == base,
    decreases n,
{
    if n > 1 {
        lemma_seq_min_ge_base(s, n - 1, base);
    }
}

proof fn lemma_seq_sum_first_rest(s: Seq<i32>, n: int, first: int, rest: int)
    requires
        1 <= n <= s.len(),
        s[0] as int == first,
        forall|i: int| 1 <= i < n ==> s[i] as int == rest,
    ensures
        seq_sum(s, n) == first + (n - 1) * rest,
    decreases n,
{
    if n == 1 {
        assert(seq_sum(s, 1) == seq_sum(s, 0) + s[0] as int);
        assert(seq_sum(s, 0) == 0int);
        assert(s[0] as int == first);
    } else {
        lemma_seq_sum_first_rest(s, n - 1, first, rest);
        assert(seq_sum(s, n - 1) == first + (n - 2) * rest);
        assert(s[n - 1] as int == rest);
        assert(seq_sum(s, n) == seq_sum(s, n - 1) + s[n - 1] as int);
        assert(seq_sum(s, n) == first + (n - 2) * rest + rest);
        assert((n - 2) * rest + rest == (n - 1) * rest) by (nonlinear_arith)
            requires n >= 2;
    }
}

proof fn lemma_seq_sum_all_but_last(s: Seq<i32>, n: int, main: int, last: int)
    requires
        1 <= n <= s.len(),
        forall|i: int| 0 <= i < n - 1 ==> s[i] as int == main,
        s[(n - 1)] as int == last,
    ensures
        seq_sum(s, n) == (n - 1) * main + last,
    decreases n,
{
    if n == 1 {
        assert(seq_sum(s, 1) == seq_sum(s, 0) + s[0] as int);
        assert(seq_sum(s, 0) == 0int);
        assert(s[0] as int == last);
    } else {
        lemma_seq_sum_constant(s, n - 1, main);
        assert(seq_sum(s, n - 1) == (n - 1) * main);
        assert(s[n - 1] as int == last);
        assert(seq_sum(s, n) == seq_sum(s, n - 1) + s[n - 1] as int);
    }
}

pub fn generate_test_case(
    base: i32,
    delta: i32,
    len: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= len <= 100_000,
        -1_000_000_000 <= base <= 1_000_000_000,
        0 <= delta,
        base as int + delta as int <= 1_000_000_000,
        (len - 1) as int * delta as int <= 2_147_483_647,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==>
            -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
        min_moves_spec(result@) >= -2_147_483_648,
        min_moves_spec(result@) <= 2_147_483_647,
{
    if mutation_kind == 1 {
        // All elements = base, min_moves = 0
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i,
                1 <= len <= 100_000,
                -1_000_000_000 <= base <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == base,
            decreases len - i,
        {
            nums.push(base);
            i = i + 1;
        }
        proof {
            lemma_seq_sum_constant(nums@, len as int, base as int);
            lemma_seq_min_constant(nums@, len as int, base as int);
            assert(min_moves_spec(nums@)
                == len as int * base as int - len as int * base as int);
        }
        nums
    } else if mutation_kind == 2 {
        // All elements = base + delta, min_moves = 0
        let val = (base + delta) as i32;
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i,
                1 <= len <= 100_000,
                val as int == base as int + delta as int,
                -1_000_000_000 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == val,
            decreases len - i,
        {
            nums.push(val);
            i = i + 1;
        }
        proof {
            lemma_seq_sum_constant(nums@, len as int, val as int);
            lemma_seq_min_constant(nums@, len as int, val as int);
            assert(min_moves_spec(nums@)
                == len as int * val as int - len as int * val as int);
        }
        nums
    } else if mutation_kind == 3 && len >= 2 {
        // All base except last = base + delta, min_moves = delta
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                nums.len() == i,
                1 <= len <= 100_000,
                -1_000_000_000 <= base <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> nums[j] == base,
            decreases len - i,
        {
            nums.push(base);
            i = i + 1;
        }
        let last = len - 1;
        let new_val = (base + delta) as i32;
        nums.set(last, new_val);
        proof {
            assert forall|j: int| 0 <= j < len as int
                implies nums[j] as int >= base as int by {
                if j < last as int {
                    assert(nums[j] == base);
                } else {
                    assert(nums[j] == new_val);
                }
            };
            lemma_seq_min_ge_base(nums@, len as int, base as int);
            lemma_seq_sum_all_but_last(
                nums@, len as int, base as int, new_val as int,
            );
            assert(seq_sum(nums@, len as int)
                == (len - 1) as int * base as int + (base as int + delta as int));
            assert((len - 1) as int * base as int + base as int
                == len as int * base as int) by (nonlinear_arith)
                requires len >= 2;
            assert(min_moves_spec(nums@) == delta as int);
        }
        nums
    } else {
        // Default (mutation 0 and fallback): first = base, rest = base + delta
        // min_moves = (len-1) * delta
        let val = (base + delta) as i32;
        let mut nums: Vec<i32> = Vec::new();
        nums.push(base);
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                nums.len() == i,
                1 <= len <= 100_000,
                -1_000_000_000 <= base <= 1_000_000_000,
                0 <= delta,
                base as int + delta as int <= 1_000_000_000,
                val as int == base as int + delta as int,
                nums[0] == base,
                forall|j: int| 1 <= j < i ==> nums[j] == val,
                forall|j: int| 0 <= j < i ==>
                    -1_000_000_000 <= #[trigger] nums[j] <= 1_000_000_000,
            decreases len - i,
        {
            nums.push(val);
            i = i + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < len as int
                implies nums[j] as int >= base as int by {
                if j == 0 {
                    assert(nums[j] == base);
                } else {
                    assert(nums[j] == val);
                }
            };
            lemma_seq_min_ge_base(nums@, len as int, base as int);
            lemma_seq_sum_first_rest(
                nums@, len as int, base as int, val as int,
            );
            assert(seq_sum(nums@, len as int)
                == base as int + (len - 1) as int * (base as int + delta as int));
            assert(base as int + (len - 1) as int * (base as int + delta as int)
                   - len as int * base as int
                == (len - 1) as int * delta as int) by (nonlinear_arith)
                requires len >= 1, delta >= 0;
            assert(min_moves_spec(nums@)
                == (len - 1) as int * delta as int);
        }
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

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let output = Solution::min_moves(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example 1: [1,2,3] -> 3
    emit(generate_test_case(1, 1, 3, 0), &mut out, &mut total);
    // Example 2: [1,1,1] -> 0
    emit(generate_test_case(1, 0, 3, 1), &mut out, &mut total);

    let seed_configs: Vec<(i32, i32, usize)> = vec![
        (0, 0, 1),
        (0, 0, 2),
        (0, 1, 2),
        (0, 1, 10),
        (-1_000_000_000, 0, 1),
        (1_000_000_000, 0, 1),
        (-1_000_000_000, 0, 5),
        (0, 0, 100_000),
        (0, 1, 100),
        (0, 21474, 100_000),
        (1, 0, 50_000),
        (-500_000_000, 500_000_000, 2),
        (-500_000_000, 500_000_000, 5),
        (999_999_999, 1, 3),
        (-1, 2, 10),
        (0, 100, 1000),
        (42, 0, 7),
        (100, 200, 50),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3];

    for &(base, delta, len) in &seed_configs {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            if mk == 3 && len < 2 { continue; }
            emit(
                generate_test_case(base, delta, len, mk),
                &mut out, &mut total,
            );
        }
    }

    while total < count {
        let len: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 100_000),
        };

        let base = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;

        let max_delta_range = (1_000_000_000i64 - base as i64).max(0);
        let max_delta_result = if len > 1 {
            (2_147_483_647i64 / (len as i64 - 1)).min(max_delta_range)
        } else {
            max_delta_range
        };

        let delta = if max_delta_result <= 0 {
            0i32
        } else if total % 5 == 0 {
            let choices = [0i64, 1, max_delta_result];
            choices[rng.gen_range_usize(0, choices.len() - 1)] as i32
        } else {
            rng.gen_range_i64(0, max_delta_result) as i32
        };

        let mk = rng.gen_range_usize(0, 3) as u8;
        let mk = if mk == 3 && len < 2 { 0 } else { mk };

        emit(
            generate_test_case(base, delta, len, mk),
            &mut out, &mut total,
        );
    }
}
