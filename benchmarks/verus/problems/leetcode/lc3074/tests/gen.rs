use vstd::prelude::*;

verus! {

// Copied from spec.rs (standalone version of Solution::sum_prefix)
pub open spec fn sum_prefix(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if n > s.len() {
        sum_prefix(s, s.len() as int)
    } else {
        sum_prefix(s, n - 1) + s[n - 1] as int
    }
}

proof fn sum_prefix_update_le(s: Seq<i32>, idx: int, new_val: i32, n: int)
    requires
        0 <= idx < s.len(),
        0 <= n <= s.len(),
        new_val <= s[idx],
    ensures
        sum_prefix(s.update(idx, new_val), n) <= sum_prefix(s, n),
    decreases n,
{
    if n > 0 {
        sum_prefix_update_le(s, idx, new_val, n - 1);
    }
}

proof fn sum_prefix_update_ge(s: Seq<i32>, idx: int, new_val: i32, n: int)
    requires
        0 <= idx < s.len(),
        0 <= n <= s.len(),
        new_val >= s[idx],
    ensures
        sum_prefix(s.update(idx, new_val), n) >= sum_prefix(s, n),
    decreases n,
{
    if n > 0 {
        sum_prefix_update_ge(s, idx, new_val, n - 1);
    }
}

pub fn generate_test_case(
    apple: Vec<i32>,
    capacity: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= apple.len() <= 50,
        1 <= capacity.len() <= 50,
        forall |i: int| 0 <= i < apple.len() ==> 1 <= #[trigger] apple[i] <= 50,
        forall |i: int| 0 <= i < capacity.len() ==> 1 <= #[trigger] capacity[i] <= 50,
        sum_prefix(apple@, apple.len() as int) <= sum_prefix(capacity@, capacity.len() as int),
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1.len() <= 50,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 50,
        sum_prefix(result.0@, result.0.len() as int) <= sum_prefix(result.1@, result.1.len() as int),
{
    if mutation_kind == 0 {
        // Identity
        (apple, capacity)
    } else if mutation_kind == 1 {
        // Minimize first apple element (reduces apple sum)
        let mut a = apple;
        proof {
            sum_prefix_update_le(a@, 0, 1i32, a@.len() as int);
        }
        a.set(0, 1);
        (a, capacity)
    } else if mutation_kind == 2 {
        // Maximize first capacity element (increases capacity sum)
        let mut c = capacity;
        proof {
            sum_prefix_update_ge(c@, 0, 50i32, c@.len() as int);
        }
        c.set(0, 50);
        (apple, c)
    } else if mutation_kind == 3 {
        // Both: minimize apple[0] and maximize capacity[0]
        let mut a = apple;
        let mut c = capacity;
        proof {
            sum_prefix_update_le(a@, 0, 1i32, a@.len() as int);
            sum_prefix_update_ge(c@, 0, 50i32, c@.len() as int);
        }
        a.set(0, 1);
        c.set(0, 50);
        (a, c)
    } else if mutation_kind == 4 && apple.len() > 1 {
        // Minimize last apple element
        let last = apple.len() - 1;
        let mut a = apple;
        proof {
            sum_prefix_update_le(a@, last as int, 1i32, a@.len() as int);
        }
        a.set(last, 1);
        (a, capacity)
    } else if mutation_kind == 5 && capacity.len() > 1 {
        // Maximize last capacity element
        let last = capacity.len() - 1;
        let mut c = capacity;
        proof {
            sum_prefix_update_ge(c@, last as int, 50i32, c@.len() as int);
        }
        c.set(last, 50);
        (apple, c)
    } else {
        // Fallback: identity
        (apple, capacity)
    }
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

fn make_valid_pair(rng: &mut Rng, n_apple: usize, n_cap: usize) -> (Vec<i32>, Vec<i32>) {
    let mut apple: Vec<i32> = (0..n_apple).map(|_| rng.gen_range_i64(1, 50) as i32).collect();
    let mut capacity: Vec<i32> = (0..n_cap).map(|_| rng.gen_range_i64(1, 50) as i32).collect();

    let mut apple_sum: i64 = apple.iter().map(|&x| x as i64).sum();
    let mut cap_sum: i64 = capacity.iter().map(|&x| x as i64).sum();

    if cap_sum < apple_sum {
        // Increase capacity elements towards 50
        for c in capacity.iter_mut() {
            if cap_sum >= apple_sum { break; }
            let add = (50 - *c) as i64;
            *c = 50;
            cap_sum += add;
        }
        // If still insufficient, reduce apple elements towards 1
        for a in apple.iter_mut().rev() {
            if cap_sum >= apple_sum { break; }
            let reduce = (*a - 1) as i64;
            apple_sum -= reduce;
            *a = 1;
        }
    }

    (apple, capacity)
}

fn emit(
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    apple: Vec<i32>,
    capacity: Vec<i32>,
    mutation_kind: u8,
    goal: usize,
) {
    use std::io::Write;
    if *count >= goal { return; }
    let (a, c) = generate_test_case(apple, capacity, mutation_kind);
    let key = format!("{:?}|{:?}", a, c);
    if !seen.insert(key) { return; }
    let output = Solution::minimum_boxes(a.clone(), c.clone());
    writeln!(out, "{}", json!({"input": {"apple": a, "capacity": c}, "output": output})).unwrap();
    *count += 1;
}

fn main() {
    use std::collections::HashSet;
    use std::io::Write;
    let mut rng = Rng::new(3074);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let goal = 100usize;

    // === LeetCode examples ===
    emit(&mut out, &mut seen, &mut count, vec![1, 3, 2], vec![4, 3, 1, 5, 2], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![5, 5, 5], vec![2, 4, 2, 7], 0, goal);

    // === Edge cases: minimal arrays ===
    emit(&mut out, &mut seen, &mut count, vec![1], vec![1], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![1], vec![50], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![50], vec![50], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![1], vec![1], 1, goal);
    emit(&mut out, &mut seen, &mut count, vec![1], vec![1], 2, goal);

    // === Exact capacity match ===
    emit(&mut out, &mut seen, &mut count, vec![25, 25], vec![50], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![10, 10, 10], vec![10, 10, 10], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![1, 1, 1, 1, 1], vec![5], 0, goal);

    // === All same values ===
    emit(&mut out, &mut seen, &mut count, vec![1; 50], vec![50; 1], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![50; 1], vec![50; 1], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![1; 10], vec![1; 10], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![50; 10], vec![50; 10], 0, goal);

    // === Max-size arrays ===
    emit(&mut out, &mut seen, &mut count, vec![1; 50], vec![1; 50], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![50; 50], vec![50; 50], 0, goal);
    emit(&mut out, &mut seen, &mut count, vec![1; 50], vec![50; 50], 0, goal);

    // === Apply mutations to interesting cases ===
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![3, 7, 2], vec![10, 5, 8]),
        (vec![10, 20, 30], vec![25, 25, 15, 5]),
        (vec![1, 2, 3, 4, 5], vec![50]),
        (vec![50], vec![1; 50]),
        (vec![5; 10], vec![10; 10]),
    ];
    for (apple, capacity) in &seeds {
        for &mk in &mutation_kinds {
            emit(&mut out, &mut seen, &mut count, apple.clone(), capacity.clone(), mk, goal);
        }
    }

    // === Small random (n_apple=1..5, n_cap=1..5) ===
    for _ in 0..15 {
        if count >= goal { break; }
        let na = rng.gen_range_usize(1, 5);
        let nc = rng.gen_range_usize(1, 5);
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }

    // === Medium random (n_apple=5..20, n_cap=5..20) ===
    for _ in 0..20 {
        if count >= goal { break; }
        let na = rng.gen_range_usize(5, 20);
        let nc = rng.gen_range_usize(5, 20);
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }

    // === Large random (n_apple=20..50, n_cap=20..50) ===
    for _ in 0..20 {
        if count >= goal { break; }
        let na = rng.gen_range_usize(20, 50);
        let nc = rng.gen_range_usize(20, 50);
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }

    // === Asymmetric: many apples, few boxes ===
    for _ in 0..10 {
        if count >= goal { break; }
        let na = rng.gen_range_usize(10, 50);
        let nc = rng.gen_range_usize(1, 5);
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }

    // === Asymmetric: few apples, many boxes ===
    for _ in 0..10 {
        if count >= goal { break; }
        let na = rng.gen_range_usize(1, 5);
        let nc = rng.gen_range_usize(10, 50);
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }

    // === Fill remaining with diverse random ===
    while count < goal {
        let size_class = rng.gen_range_usize(0, 3);
        let (na, nc) = match size_class {
            0 => (rng.gen_range_usize(1, 5), rng.gen_range_usize(1, 5)),
            1 => (rng.gen_range_usize(5, 20), rng.gen_range_usize(5, 20)),
            2 => (rng.gen_range_usize(20, 50), rng.gen_range_usize(20, 50)),
            _ => (rng.gen_range_usize(1, 50), rng.gen_range_usize(1, 50)),
        };
        let (apple, capacity) = make_valid_pair(&mut rng, na, nc);
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(&mut out, &mut seen, &mut count, apple, capacity, mk, goal);
    }
}
