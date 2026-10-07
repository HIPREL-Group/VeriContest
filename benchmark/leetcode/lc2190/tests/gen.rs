use vstd::prelude::*;

verus! {

pub open spec fn count_following(nums: Seq<i32>, key: i32, target: i32, end: int) -> int
    recommends
        0 <= end <= nums.len(),
    decreases end,
{
    if end <= 1 {
        0
    } else {
        count_following(nums, key, target, end - 1)
            + if nums[end - 2] == key && nums[end - 1] == target { 1int } else { 0int }
    }
}

pub open spec fn all_followers_leq_target(nums: Seq<i32>, key: i32, n: int, target: int) -> bool {
    count_following(nums, key, key, n) <= count_following(nums, key, target as i32, n)
        && (forall|t: int| 1 <= t <= 1000 ==>
            #[trigger] count_following(nums, key, t as i32, n) <= count_following(nums, key, target as i32, n))
}

proof fn lemma_count_following_all_key(
    nums: Seq<i32>,
    key: i32,
    end: int,
    target: i32,
)
    requires
        2 <= end <= nums.len(),
        (forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == key),
        1 <= target <= 1000,
    ensures
        count_following(nums, key, target, end) == if target == key { end - 1 } else { 0int },
    decreases end,
{
    if end <= 2 {
        assert(end == 2);
        assert(count_following(nums, key, target, 1) == 0);
        assert(
            count_following(nums, key, target, end)
                == count_following(nums, key, target, 1)
                    + (if nums[0] == key && nums[1] == target { 1int } else { 0int })
        );
        assert(nums[0] == key && nums[1] == key);
        if target == key {
            assert(count_following(nums, key, target, end) == 1);
            assert(if target == key { end - 1 } else { 0int } == 1);
        } else {
            assert(!(nums[0] == key && nums[1] == target));
            assert(count_following(nums, key, target, end) == 0);
            assert(if target == key { end - 1 } else { 0int } == 0);
        }
    } else {
        lemma_count_following_all_key(nums, key, end - 1, target);
        assert(count_following(nums, key, target, end)
            == count_following(nums, key, target, end - 1)
                + if nums[end - 2] == key && nums[end - 1] == target { 1int } else { 0int });
        assert(nums[end - 2] == key && nums[end - 1] == key);
        if target == key {
            assert(count_following(nums, key, target, end - 1) == end - 2);
            assert(count_following(nums, key, target, end) == end - 1);
        } else {
            assert(!(nums[end - 2] == key && nums[end - 1] == target));
            assert(count_following(nums, key, target, end) == count_following(nums, key, target, end - 1));
            assert(count_following(nums, key, target, end - 1) == 0);
        }
    }
}

proof fn lemma_unique_argmax_all_key(nums: Seq<i32>, key: i32, n: int)
    requires
        2 <= n <= nums.len(),
        n == nums.len(),
        (forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == key),
        1 <= key <= 1000,
    ensures
        forall|t1: int, t2: int|
            1 <= t1 <= 1000 && 1 <= t2 <= 1000
                && #[trigger] all_followers_leq_target(nums, key, n, t1)
                && #[trigger] all_followers_leq_target(nums, key, n, t2)
                ==> t1 == t2,
{
    assert forall|t1: int, t2: int|
        1 <= t1 <= 1000 && 1 <= t2 <= 1000
            && all_followers_leq_target(nums, key, n, t1)
            && all_followers_leq_target(nums, key, n, t2)
            implies t1 == t2 by {
        lemma_count_following_all_key(nums, key, n, key);
        assert(count_following(nums, key, key, n) == n - 1);
        lemma_count_following_all_key(nums, key, n, t1 as i32);
        lemma_count_following_all_key(nums, key, n, t2 as i32);
        let c1 = count_following(nums, key, t1 as i32, n);
        let c2 = count_following(nums, key, t2 as i32, n);
        if t1 != key as int {
            assert(t1 as i32 != key);
            assert(c1 == 0);
            assert(all_followers_leq_target(nums, key, n, t1));
            assert(count_following(nums, key, key, n) <= count_following(nums, key, t1 as i32, n));
            assert(n - 1 <= 0);
            assert(false);
        } else if t2 != key as int {
            assert(t2 as i32 != key);
            assert(c2 == 0);
            assert(all_followers_leq_target(nums, key, n, t2));
            assert(count_following(nums, key, key, n) <= count_following(nums, key, t2 as i32, n));
            assert(n - 1 <= 0);
            assert(false);
        } else {
            assert(t1 == key as int);
            assert(t2 == key as int);
            assert(t1 == t2);
        }
    };
}

pub fn generate_test_case(
    elems: Vec<i32>,
    key: i32,
    key_pos: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= elems.len() <= 1000,
        1 <= key <= 1000,
        forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
        key_pos < elems.len() - 1,
    ensures
        2 <= result.0.len() <= 1000,
        1 <= result.1 <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        exists|i: int| 0 <= i < result.0.len() - 1 && result.0[i] == result.1,
        forall|t1: int, t2: int|
            1 <= t1 <= 1000 && 1 <= t2 <= 1000
                && #[trigger] all_followers_leq_target(result.0@, result.1, result.0.len() as int, t1)
                && #[trigger] all_followers_leq_target(result.0@, result.1, result.0.len() as int, t2)
                ==> t1 == t2,
{
    let ghost _ = (mutation_kind, key_pos);
    let mut nums = elems;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            nums.len() == elems.len(),
            2 <= nums.len() <= 1000,
            1 <= key <= 1000,
            forall|j: int| 0 <= j < i ==> nums[j] == key,
            forall|j: int| i <= j < nums.len() ==> nums[j] == elems[j],
        decreases nums.len() - i,
    {
        nums.set(i, key);
        i += 1;
    }
    assert(nums[key_pos as int] == key);
    proof {
        assert(forall|j: int| 0 <= j < nums.len() as int ==> nums@[j] == key);
        lemma_unique_argmax_all_key(nums@, key, nums.len() as int);
    }
    (nums, key)
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

fn gen(elems: Vec<i32>, key: i32, key_pos: usize, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(elems, key, key_pos, mutation_kind)
}

/// One JSONL line (Rust `Debug` for `nums` is JSON-compatible for i32 lists).
fn testcase_json_line(nums: &[i32], key: i32, output: i32) -> String {
    format!(r#"{{"input":{{"nums":{:?},"key":{}}},"output":{}}}"#, nums, key, output)
}

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2190);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, key: i32, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target { return; }
        let k = format!("{:?},{}", nums, key);
        if !seen.insert(k) { return; }
        let output = Solution::most_frequent(nums.clone(), key);
        writeln!(out, "{}", testcase_json_line(&nums, key, output)).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 100, 200, 1, 100], 1),
        (vec![2, 2, 2, 2, 3], 2),
    ];
    for (nums, key) in examples {
        emit(nums, key, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with known patterns
    let seed_arrays: Vec<(Vec<i32>, i32, usize)> = vec![
        (vec![1, 2], 1, 0),
        (vec![5, 5, 5], 5, 0),
        (vec![1, 1, 2, 2, 3, 3], 1, 0),
        (vec![1000, 1, 1000, 1], 1000, 0),
        (vec![1, 1000], 1, 0),
        (vec![500, 500, 500, 500], 500, 0),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 1, 0),
        (vec![3, 3, 3, 3, 3, 2], 3, 0),
        (vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 2], 1, 0),
        (vec![999, 1000, 999, 1000], 999, 0),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Apply every mutation to every seed array
    for (elems, key, kp) in &seed_arrays {
        for &mk in &mutation_kinds {
            let (nums, k) = gen(elems.clone(), *key, *kp, mk);
            emit(nums, k, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with varied sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 5),       // tiny
        (6, 20),      // small
        (21, 100),    // medium
        (101, 500),   // large
        (501, 1000),  // max
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..12 {
            if count >= count_target { break; }
            let len = rng.gen_range_usize(lo, hi);
            let elems = random_elems(&mut rng, len);
            let key = rng.gen_range_i64(1, 1000) as i32;
            let key_pos = rng.gen_range_usize(0, len - 2);
            let mk = rng.gen_range_usize(0, 5) as u8;
            let (nums, k) = gen(elems, key, key_pos, mk);
            emit(nums, k, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random inputs
    while count < count_target {
        let len = rng.gen_range_usize(2, 1000);
        let elems = random_elems(&mut rng, len);
        let key = rng.gen_range_i64(1, 1000) as i32;
        let key_pos = rng.gen_range_usize(0, len - 2);
        let mk = rng.gen_range_usize(0, 5) as u8;
        let (nums, k) = gen(elems, key, key_pos, mk);
        emit(nums, k, &mut seen, &mut out, &mut count);
    }
}
