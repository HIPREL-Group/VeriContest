use vstd::prelude::*;

verus! {

pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occurrences(s.drop_last(), value)
            + if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

proof fn count_push_lemma(s: Seq<i32>, v: i32, x: i32)
    ensures
        count_occurrences(s.push(v), x)
            == count_occurrences(s, x) + if v == x { 1nat } else { 0nat }
{
    assert(s.push(v).drop_last() =~= s);
}

pub fn generate_test_case(
    a_val: i32,
    b_val: i32,
    pairs: &Vec<i32>,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        a_val != b_val,
        pairs.len() <= 14_999,
        forall|i: int, j: int|
            0 <= i < pairs.len() && 0 <= j < pairs.len() && i != j
                ==> pairs[i] != pairs[j],
        forall|i: int|
            0 <= i < pairs.len()
                ==> #[trigger] pairs[i] != a_val && pairs[i] != b_val,
    ensures
        2 <= nums.len() <= 30_000,
        forall|i: int| 0 <= i < nums.len()
            ==> -2_147_483_648 <= #[trigger] nums[i] <= 2_147_483_647,
        exists|a: i32, b: i32| {
            a != b
            && count_occurrences(nums@, a) == 1
            && count_occurrences(nums@, b) == 1
            && forall|x: i32| x != a && x != b
                ==> count_occurrences(nums@, x) == 0
                    || count_occurrences(nums@, x) == 2
        },
{
    let first: i32 = if mutation_kind % 2 == 0 { a_val } else { b_val };
    let second: i32 = if mutation_kind % 2 == 0 { b_val } else { a_val };

    let mut nums: Vec<i32> = Vec::new();

    let ghost s_empty = nums@;
    nums.push(first);
    let ghost s_one = nums@;
    nums.push(second);

    proof {
        count_push_lemma(s_empty, first, first);
        count_push_lemma(s_empty, first, second);
        count_push_lemma(s_one, second, first);
        count_push_lemma(s_one, second, second);
    }

    // Establish initial invariant: pairs and other values have count 0
    proof {
        assert forall|j: int| 0 <= j < pairs.len() as int
            implies count_occurrences(nums@, #[trigger] pairs[j]) == 0nat
        by {
            count_push_lemma(s_empty, first, pairs[j]);
            count_push_lemma(s_one, second, pairs[j]);
        };
        assert forall|x: i32|
            x != a_val && x != b_val
            && (forall|j: int| 0 <= j < pairs.len() as int
                    ==> x != #[trigger] pairs[j])
            implies count_occurrences(nums@, x) == 0nat
        by {
            count_push_lemma(s_empty, first, x);
            count_push_lemma(s_one, second, x);
        };
    }

    let mut pi: usize = 0;
    while pi < pairs.len()
        invariant
            0 <= pi <= pairs.len(),
            nums.len() == 2 + 2 * pi,
            pairs.len() <= 14_999,
            first != second,
            a_val != b_val,
            (first == a_val && second == b_val) || (first == b_val && second == a_val),
            count_occurrences(nums@, a_val) == 1nat,
            count_occurrences(nums@, b_val) == 1nat,
            forall|j: int| 0 <= j < pi as int
                ==> count_occurrences(nums@, #[trigger] pairs[j]) == 2nat,
            forall|j: int| pi as int <= j < pairs.len() as int
                ==> count_occurrences(nums@, #[trigger] pairs[j]) == 0nat,
            forall|x: i32|
                x != a_val && x != b_val
                && (forall|j: int| 0 <= j < pairs.len() as int
                        ==> x != #[trigger] pairs[j])
                ==> count_occurrences(nums@, x) == 0nat,
            forall|i: int| 0 <= i < nums.len() as int
                ==> -2_147_483_648i32 <= #[trigger] nums[i] <= 2_147_483_647i32,
            forall|i: int, j: int|
                0 <= i < pairs.len() && 0 <= j < pairs.len() && i != j
                    ==> pairs[i] != pairs[j],
            forall|i: int| 0 <= i < pairs.len()
                ==> #[trigger] pairs[i] != a_val && pairs[i] != b_val,
        decreases pairs.len() - pi,
    {
        let v = pairs[pi];

        let ghost s0 = nums@;
        nums.push(v);
        proof {
            count_push_lemma(s0, v, a_val);
            count_push_lemma(s0, v, b_val);
            count_push_lemma(s0, v, v);
            assert forall|j: int| 0 <= j < pi as int
                implies count_occurrences(nums@, #[trigger] pairs[j]) == 2nat
            by { count_push_lemma(s0, v, pairs[j]); };
            assert forall|j: int| (pi as int) + 1 <= j < pairs.len() as int
                implies count_occurrences(nums@, #[trigger] pairs[j]) == 0nat
            by { count_push_lemma(s0, v, pairs[j]); };
            assert forall|x: i32|
                x != a_val && x != b_val
                && (forall|j: int| 0 <= j < pairs.len() as int ==> x != #[trigger] pairs[j])
                implies count_occurrences(nums@, x) == 0nat
            by { count_push_lemma(s0, v, x); };
        }

        let ghost s1 = nums@;
        nums.push(v);
        proof {
            count_push_lemma(s1, v, a_val);
            count_push_lemma(s1, v, b_val);
            count_push_lemma(s1, v, v);
            assert forall|j: int| 0 <= j < pi as int
                implies count_occurrences(nums@, #[trigger] pairs[j]) == 2nat
            by { count_push_lemma(s1, v, pairs[j]); };
            assert forall|j: int| (pi as int) + 1 <= j < pairs.len() as int
                implies count_occurrences(nums@, #[trigger] pairs[j]) == 0nat
            by { count_push_lemma(s1, v, pairs[j]); };
            assert forall|x: i32|
                x != a_val && x != b_val
                && (forall|j: int| 0 <= j < pairs.len() as int ==> x != #[trigger] pairs[j])
                implies count_occurrences(nums@, x) == 0nat
            by { count_push_lemma(s1, v, x); };
        }

        pi = pi + 1;
    }

    proof {
        assert forall|x: i32| x != a_val && x != b_val
            implies count_occurrences(nums@, x) == 0nat
                || count_occurrences(nums@, x) == 2nat
        by {
            if exists|j: int| 0 <= j < pairs.len() as int && x == pairs[j] {
                let j = choose|j: int| 0 <= j < pairs.len() as int && x == pairs[j];
                assert(count_occurrences(nums@, pairs[j]) == 2nat);
            } else {
                assert(forall|j: int| 0 <= j < pairs.len() as int ==> x != #[trigger] pairs[j]);
                assert(count_occurrences(nums@, x) == 0nat);
            }
        };
        assert(
            a_val != b_val
            && count_occurrences(nums@, a_val) == 1
            && count_occurrences(nums@, b_val) == 1
            && (forall|x: i32| x != a_val && x != b_val
                ==> count_occurrences(nums@, x) == 0 || count_occurrences(nums@, x) == 2)
        );
    }

    nums
}

} // verus!

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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
    use std::collections::HashSet;
    use std::io::Write;
    let mut rng = Rng::new(260);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;
    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", nums);
        if *count >= target || !seen.insert(key) { return; }
        let output = Solution::single_number(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };
    for ex in vec![vec![1,2,1,3,2,5], vec![-1,0], vec![0,1]] {
        emit(ex, &mut seen, &mut out, &mut count);
    }
    let boundary_seeds: Vec<(i32, i32, Vec<i32>)> = vec![
        (i32::MIN, i32::MAX, vec![]), (0, 1, vec![]), (-1, 1, vec![]),
        (i32::MIN, 0, vec![1]), (i32::MAX, 0, vec![-1]),
        (42, -42, vec![0, 1, -1, 100, -100]),
        (1, 2, vec![3, 4, 5, 6, 7, 8, 9, 10]),
    ];
    for (a, b, pairs) in &boundary_seeds {
        for mk in 0..2u8 {
            let nums = generate_test_case(*a, *b, pairs, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }
    let size_classes: [(usize, usize); 6] = [
        (0, 0), (1, 5), (5, 50), (50, 500), (500, 5_000), (5_000, 14_999),
    ];
    for &(lo, hi) in &size_classes {
        for mk in 0..2u8 {
            let np = rng.gen_range_usize(lo, hi);
            let a = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
            let mut b = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
            while b == a { b = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32; }
            let mut pairs: Vec<i32> = Vec::new();
            let mut used = HashSet::new();
            used.insert(a); used.insert(b);
            while pairs.len() < np {
                let v = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
                if !used.contains(&v) { used.insert(v); pairs.push(v); }
            }
            let nums = generate_test_case(a, b, &pairs, mk);
            emit(nums, &mut seen, &mut out, &mut count);
        }
    }
    while count < target {
        let np = match count % 5 {
            0 => 0, 1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 100), 3 => rng.gen_range_usize(100, 1_000),
            _ => rng.gen_range_usize(1_000, 5_000),
        };
        let a = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
        let mut b = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
        while b == a { b = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32; }
        let mut pairs: Vec<i32> = Vec::new();
        let mut used = HashSet::new();
        used.insert(a); used.insert(b);
        while pairs.len() < np {
            let v = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
            if !used.contains(&v) { used.insert(v); pairs.push(v); }
        }
        let mk = (count % 2) as u8;
        let nums = generate_test_case(a, b, &pairs, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
