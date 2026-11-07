use vstd::prelude::*;

verus! {

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn array_value_upto(s: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else { array_value_upto(s, n - 1) + abs_diff(s[n - 1] as int, s[n] as int) }
}

pub open spec fn array_value(s: Seq<i32>) -> int {
    array_value_upto(s, s.len() as int - 1)
}

pub open spec fn reversal_gain(s: Seq<i32>, l: int, r: int) -> int {
    let n = s.len() as int;
    let left_change = if l > 0 {
        abs_diff(s[l - 1] as int, s[r] as int) - abs_diff(s[l - 1] as int, s[l] as int)
    } else { 0int };
    let right_change = if r < n - 1 {
        abs_diff(s[l] as int, s[r + 1] as int) - abs_diff(s[r] as int, s[r + 1] as int)
    } else { 0int };
    left_change + right_change
}

proof fn abs_diff_bound(a: int, b: int, bound: int)
    requires
        -bound <= a <= bound,
        -bound <= b <= bound,
        bound >= 0,
    ensures
        abs_diff(a, b) <= 2 * bound,
{
}

proof fn array_value_upto_bound(s: Seq<i32>, n: int, bound: int)
    requires
        bound >= 0,
        n >= 0,
        n < s.len() as int,
        forall|i: int| 0 <= i < s.len() ==> -bound <= #[trigger] (s[i] as int) <= bound,
    ensures
        0 <= array_value_upto(s, n),
        array_value_upto(s, n) <= n * (2 * bound),
    decreases n,
{
    if n > 0 {
        array_value_upto_bound(s, n - 1, bound);
        abs_diff_bound(s[n - 1] as int, s[n] as int, bound);
        assert(array_value_upto(s, n - 1) <= (n - 1) * (2 * bound));
        assert(abs_diff(s[n - 1] as int, s[n] as int) <= 2 * bound);
        assert((n - 1) * (2 * bound) + 2 * bound == n * (2 * bound)) by(nonlinear_arith) requires n >= 1, bound >= 0;
    }
}

proof fn reversal_gain_bound(s: Seq<i32>, l: int, r: int, bound: int)
    requires
        bound >= 0,
        s.len() >= 2,
        0 <= l <= r < s.len() as int,
        forall|i: int| 0 <= i < s.len() ==> -bound <= #[trigger] (s[i] as int) <= bound,
    ensures
        reversal_gain(s, l, r) <= 4 * bound,
{
    if l > 0 {
        abs_diff_bound(s[l - 1] as int, s[r] as int, bound);
        abs_diff_bound(s[l - 1] as int, s[l] as int, bound);
    }
    if r < s.len() as int - 1 {
        abs_diff_bound(s[l] as int, s[r + 1] as int, bound);
        abs_diff_bound(s[r] as int, s[r + 1] as int, bound);
    }
}

proof fn overflow_proof(s: Seq<i32>, bound: int)
    requires
        bound >= 0,
        s.len() >= 2,
        (s.len() as int - 1) * (2 * bound) + 4 * bound <= i32::MAX as int,
        forall|i: int| 0 <= i < s.len() ==> -bound <= #[trigger] (s[i] as int) <= bound,
    ensures
        forall|l: int, r: int| 0 <= l && l <= r && r < s.len() ==>
            array_value(s) + #[trigger] reversal_gain(s, l, r) <= i32::MAX as int,
{
    array_value_upto_bound(s, s.len() as int - 1, bound);
    assert forall|l: int, r: int| 0 <= l && l <= r && r < s.len() implies
        array_value(s) + #[trigger] reversal_gain(s, l, r) <= i32::MAX as int
    by {
        reversal_gain_bound(s, l, r, bound);
    };
}

// Values bounded by 1000 ensure overflow is impossible for arrays up to 30000:
// array_value <= 29999 * 2000 = 59_998_000
// reversal_gain <= 4000
// total <= 60_002_000 << 2_147_483_647
pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 30000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        2 <= result@.len() <= 30000,
        forall|i: int| 0 <= i < result@.len() ==> -100000 <= #[trigger] result@[i] <= 100000,
        forall|l: int, r: int| 0 <= l && l <= r && r < result@.len() ==>
            array_value(result@) + #[trigger] reversal_gain(result@, l, r) <= i32::MAX as int,
{
    let res = if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut a = nums;
        a.set(0, 0);
        a
    } else if mutation_kind == 2 {
        let mut a = nums;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 3 {
        let mut a = nums;
        a.set(0, 1000);
        a
    } else if mutation_kind == 4 {
        let mut a = nums;
        a.set(0, -1000);
        a
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut a = nums;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == nums.len(),
                2 <= a.len() <= 30000,
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == 0i32,
                forall|j: int| i <= j < a.len() ==> -1000 <= #[trigger] a[j] <= 1000,
            decreases a.len() - i,
        {
            a.set(i, 0);
            i = i + 1;
        }
        a
    } else if mutation_kind == 6 {
        // negate all elements
        let mut a = nums;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == nums.len(),
                2 <= a.len() <= 30000,
                forall|j: int| 0 <= j < i ==> -1000 <= #[trigger] a[j] <= 1000,
                forall|j: int| i <= j < a.len() ==> -1000 <= #[trigger] a[j] <= 1000,
            decreases a.len() - i,
        {
            a.set(i, -a[i]);
            i = i + 1;
        }
        a
    } else if mutation_kind == 7 && nums.len() < 30000 {
        let mut a = nums;
        a.push(0);
        a
    } else if mutation_kind == 8 && nums.len() > 2 {
        let mut a = nums;
        a.pop();
        a
    } else {
        nums
    };
    proof {
        overflow_proof(res@, 1000);
    }
    res
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    v
}

fn random_nums_in_range(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1330);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! gen_emit {
        ($nums:expr, $mk:expr) => {{
            if count < goal {
                let mutated = generate_test_case($nums, $mk);
                let key = format!("{:?}", mutated);
                if seen.insert(key) {
                    let output = Solution::max_value_after_reverse(mutated.clone());
                    writeln!(out, "{}", json!({"input": {"nums": mutated}, "output": output})).unwrap();
                    count += 1;
                }
            }
        }};
    }

    // Example inputs from description.md
    gen_emit!(vec![2, 3, 1, 5, 4], 0);
    gen_emit!(vec![2, 4, 9, 24, 2, 1, 10], 0);

    // Edge cases: minimum length
    let fixed_seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![1, -1],
        vec![-1000, 1000],
        vec![1000, -1000],
        vec![1000, 1000],
        vec![-1000, -1000],
        vec![0, 1000],
        vec![0, -1000],
        // Small arrays with interesting patterns
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 3, 2],
        vec![1, 100, 1],
        vec![-1, -100, -1],
        vec![1, -1, 1, -1],
        vec![1000, -1000, 1000, -1000],
        // Sorted ascending
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        // Sorted descending
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        // All same
        vec![42, 42, 42, 42, 42],
        // V-shape
        vec![100, 50, 0, 50, 100],
        // Inverse V-shape
        vec![0, 50, 100, 50, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for seed_arr in &fixed_seeds {
        for &mk in &mutation_kinds {
            gen_emit!(seed_arr.clone(), mk);
        }
    }

    // Small random arrays with all mutations
    for _ in 0..5 {
        let len = rng.gen_range_usize(2, 10);
        let arr = random_nums(&mut rng, len);
        for &mk in &mutation_kinds {
            gen_emit!(arr.clone(), mk);
        }
    }

    // Medium random arrays
    for _ in 0..5 {
        let len = rng.gen_range_usize(10, 100);
        let arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        gen_emit!(arr, mk);
    }

    // Large random arrays
    for _ in 0..5 {
        let len = rng.gen_range_usize(100, 1000);
        let arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        gen_emit!(arr, mk);
    }

    // Arrays with narrow value range (small differences)
    for _ in 0..3 {
        let len = rng.gen_range_usize(5, 50);
        let arr = random_nums_in_range(&mut rng, len, -10, 10);
        let mk = rng.gen_range_usize(0, 6) as u8;
        gen_emit!(arr, mk);
    }

    // Arrays with extreme values only
    for _ in 0..3 {
        let len = rng.gen_range_usize(2, 20);
        let mut arr = Vec::with_capacity(len);
        for _ in 0..len {
            if rng.gen_range_usize(0, 1) == 0 {
                arr.push(-1000i32);
            } else {
                arr.push(1000i32);
            }
        }
        let mk = rng.gen_range_usize(0, 6) as u8;
        gen_emit!(arr, mk);
    }

    // Fill remaining with random sizes and mutations
    while count < goal {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),          // tiny
            1 => rng.gen_range_usize(2, 20),         // small
            2 => rng.gen_range_usize(20, 200),       // medium
            3 => rng.gen_range_usize(200, 2000),     // large
            _ => rng.gen_range_usize(2000, 30000),  // max
        };
        let arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        gen_emit!(arr, mk);
    }
}
