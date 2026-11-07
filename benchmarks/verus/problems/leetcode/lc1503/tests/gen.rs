use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, raw_left: Vec<i32>, raw_right: Vec<i32>) -> (result: (i32, Vec<i32>, Vec<i32>))
    ensures 1 <= result.0 <= 10000, 1 <= result.1.len() + result.2.len() <= result.0 + 1,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= result.0,
        forall|i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] <= result.0,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall|i: int, j: int| 0 <= i < j < result.2.len() ==> result.2[i] != result.2[j],
        forall|i: int, j: int| 0 <= i < result.1.len() && 0 <= j < result.2.len() ==> result.1[i] != result.2[j],
{
    let n = if n < 1 { 1 } else if n > 10000 { 10000 } else { n };
    let mut seen: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i <= n as usize
        invariant i <= n + 1, 1 <= n <= 10000, seen.len() == i,
        decreases n + 1 - i,
    { seen.push(false); i += 1; }
    let mut left: Vec<i32> = Vec::new();
    let end = if raw_left.len() > n as usize + 1 { n as usize + 1 } else { raw_left.len() };
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw_left.len(), end <= n + 1, 1 <= n <= 10000,
            seen.len() == n + 1, left.len() <= i,
            forall|j: int| 0 <= j < left.len() ==> 0 <= #[trigger] left[j] <= n,
            forall|j: int| 0 <= j < left.len() ==> #[trigger] seen[left[j] as int],
            forall|j: int, k: int| 0 <= j < k < left.len() ==> left[j] != left[k],
        decreases end - i,
    {
        let v = raw_left[i];
        let v = if v < 0 { 0 } else if v > n { n } else { v };
        if !seen[v as usize] {
            assert forall|j: int| 0 <= j < left.len() implies #[trigger] left[j] != v by { assert(seen[left[j] as int]); }
            seen.set(v as usize, true); left.push(v);
        }
        i += 1;
    }
    let mut right: Vec<i32> = Vec::new();
    let end = if raw_right.len() > n as usize + 1 { n as usize + 1 } else { raw_right.len() };
    let mut i = 0usize;
    while i < end && left.len() + right.len() < n as usize + 1
        invariant i <= end <= raw_right.len(), end <= n + 1, 1 <= n <= 10000,
            seen.len() == n + 1, left.len() + right.len() <= n + 1,
            forall|j: int| 0 <= j < left.len() ==> 0 <= #[trigger] left[j] <= n,
            forall|j: int| 0 <= j < right.len() ==> 0 <= #[trigger] right[j] <= n,
            forall|j: int| 0 <= j < left.len() ==> #[trigger] seen[left[j] as int],
            forall|j: int| 0 <= j < right.len() ==> #[trigger] seen[right[j] as int],
            forall|j: int, k: int| 0 <= j < k < left.len() ==> left[j] != left[k],
            forall|j: int, k: int| 0 <= j < k < right.len() ==> right[j] != right[k],
            forall|j: int, k: int| 0 <= j < left.len() && 0 <= k < right.len() ==> left[j] != right[k],
        decreases end - i,
    {
        let v = raw_right[i];
        let v = if v < 0 { 0 } else if v > n { n } else { v };
        if !seen[v as usize] {
            assert forall|j: int| 0 <= j < left.len() implies #[trigger] left[j] != v by { assert(seen[left[j] as int]); }
            assert forall|j: int| 0 <= j < right.len() implies #[trigger] right[j] != v by { assert(seen[right[j] as int]); }
            seen.set(v as usize, true); right.push(v);
        }
        i += 1;
    }
    if left.len() + right.len() == 0 { left.push(0); }
    (n, left, right)
}


pub fn generate_candidate(
    n: i32,
    left: Vec<i32>,
    right: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 10_000,
        left.len() + right.len() >= 1,
        left.len() + right.len() <= n + 1,
        forall |i: int| 0 <= i < left.len() ==> 0 <= #[trigger] left[i] <= n,
        forall |i: int| 0 <= i < right.len() ==> 0 <= #[trigger] right[i] <= n,
    ensures
        1 <= result.0 <= 10_000,
        result.1.len() + result.2.len() >= 1,
        result.1.len() + result.2.len() <= result.0 + 1,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= result.0,
        forall |i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] <= result.0,
{
    if mutation_kind == 0 {
        // identity
        (n, left, right)
    } else if mutation_kind == 1 && left.len() > 0 {
        // set first left element to 0
        let mut l = left;
        l.set(0, 0);
        (n, l, right)
    } else if mutation_kind == 2 && left.len() > 0 {
        // set first left element to n
        let mut l = left;
        l.set(0, n);
        (n, l, right)
    } else if mutation_kind == 3 && right.len() > 0 {
        // set first right element to 0
        let mut r = right;
        r.set(0, 0);
        (n, left, r)
    } else if mutation_kind == 4 && right.len() > 0 {
        // set first right element to n
        let mut r = right;
        r.set(0, n);
        (n, left, r)
    } else if mutation_kind == 5 && left.len() > 0 && left[0] < n {
        // nudge first left element up
        let mut l = left;
        let v = l[0] + 1;
        l.set(0, v);
        (n, l, right)
    } else if mutation_kind == 6 && left.len() > 0 && left[0] > 0 {
        // nudge first left element down
        let mut l = left;
        let v = l[0] - 1;
        l.set(0, v);
        (n, l, right)
    } else if mutation_kind == 7 && right.len() > 0 && right[0] < n {
        // nudge first right element up
        let mut r = right;
        let v = r[0] + 1;
        r.set(0, v);
        (n, left, r)
    } else if mutation_kind == 8 && right.len() > 0 && right[0] > 0 {
        // nudge first right element down
        let mut r = right;
        let v = r[0] - 1;
        r.set(0, v);
        (n, left, r)
    } else if mutation_kind == 9 && left.len() >= 2 {
        // swap first and last of left
        let mut l = left;
        let last = l.len() - 1;
        let first_val = l[0];
        let last_val = l[last];
        l.set(0, last_val);
        l.set(last, first_val);
        (n, l, right)
    } else if mutation_kind == 10 && right.len() >= 2 {
        // swap first and last of right
        let mut r = right;
        let last = r.len() - 1;
        let first_val = r[0];
        let last_val = r[last];
        r.set(0, last_val);
        r.set(last, first_val);
        (n, left, r)
    } else if mutation_kind == 11 && n < 10_000 {
        // increase n by 1 (all elements still in [0, n+1])
        (n + 1, left, right)
    } else if mutation_kind == 12 && n > 1 {
        // decrease n by 1 if all elements fit
        let new_n = n - 1;
        let mut all_fit = true;
        let mut i: usize = 0;
        while i < left.len()
            invariant
                0 <= i <= left.len(),
                all_fit ==> forall |j: int| 0 <= j < i ==> #[trigger] left[j] <= new_n,
                forall |j: int| 0 <= j < left.len() ==> 0 <= #[trigger] left[j] <= n,
                new_n == n - 1,
                1 <= new_n,
            decreases left.len() - i,
        {
            if left[i] > new_n {
                all_fit = false;
            }
            i += 1;
        }
        let mut j: usize = 0;
        while j < right.len()
            invariant
                0 <= j <= right.len(),
                all_fit ==> forall |k: int| 0 <= k < left.len() ==> #[trigger] left[k] <= new_n,
                all_fit ==> forall |k: int| 0 <= k < j ==> #[trigger] right[k] <= new_n,
                forall |k: int| 0 <= k < right.len() ==> 0 <= #[trigger] right[k] <= n,
                forall |k: int| 0 <= k < left.len() ==> 0 <= #[trigger] left[k] <= n,
                new_n == n - 1,
                1 <= new_n,
            decreases right.len() - j,
        {
            if right[j] > new_n {
                all_fit = false;
            }
            j += 1;
        }
        if all_fit && left.len() + right.len() <= (new_n + 1) as usize {
            (new_n, left, right)
        } else {
            (n, left, right)
        }
    } else {
        // fallback: identity
        (n, left, right)
    }
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn mutate(n: i32, left: Vec<i32>, right: Vec<i32>, mk: u8) -> (i32, Vec<i32>, Vec<i32>) {
    generate_candidate(n, left, right, mk)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 13;

    let mut emit = |n: i32, left: Vec<i32>, right: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{}:{:?}:{:?}", n, left, right);
        if !seen.insert(key) { return; }
        let (n, left, right) = generate_test_case(n, left, right);
        let output = Solution::get_last_moment(n, left.clone(), right.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "left": left, "right": right},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(4, vec![4, 3], vec![0, 1], &mut seen, &mut out, &mut count);
    emit(7, vec![], vec![0, 1, 2, 3, 4, 5, 6, 7], &mut seen, &mut out, &mut count);
    emit(7, vec![0, 1, 2, 3, 4, 5, 6, 7], vec![], &mut seen, &mut out, &mut count);

    // Interesting seed cases
    let seeds: Vec<(i32, Vec<i32>, Vec<i32>)> = vec![
        (1, vec![0], vec![1]),
        (1, vec![1], vec![0]),
        (1, vec![0], vec![]),
        (1, vec![], vec![0]),
        (1, vec![1], vec![]),
        (1, vec![], vec![1]),
        (10, vec![5], vec![5]),
        (10, vec![0, 10], vec![5]),
        (10, vec![10], vec![0]),
        (100, vec![50, 100], vec![0, 50]),
        (10_000, vec![10_000], vec![0]),
        (10_000, vec![0], vec![10_000]),
        (10_000, vec![5000], vec![5000]),
        (5, vec![1, 2, 3], vec![4, 5]),
        (3, vec![0, 1, 2, 3], vec![]),
        (3, vec![], vec![0, 1, 2, 3]),
    ];

    // Apply every mutation to every seed
    for (sn, sl, sr) in &seeds {
        for mk in 0..num_mutations {
            if count >= target_count { break; }
            let (rn, rl, rr) = mutate(*sn, sl.clone(), sr.clone(), mk);
            emit(rn, rl, rr, &mut seen, &mut out, &mut count);
        }
        if count >= target_count { break; }
    }

    // Random seeds across size classes with random mutations
    for i in 0..200 {
        if count >= target_count { break; }
        let n = match i % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 20) as i32,       // small
            2 => rng.gen_range_i64(21, 200) as i32,     // medium
            3 => rng.gen_range_i64(201, 2000) as i32,   // large
            _ => rng.gen_range_i64(2001, 10_000) as i32, // max
        };
        let max_total = (n + 1).min(100) as usize; // cap for performance
        let total = rng.gen_range_usize(1, max_total);
        let left_len = rng.gen_range_usize(0, total);
        let right_len = total - left_len;
        let left = random_vec(&mut rng, left_len, 0, n);
        let right = random_vec(&mut rng, right_len, 0, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (rn, rl, rr) = mutate(n, left, right, mk);
        emit(rn, rl, rr, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random cases
    while count < target_count {
        let n = rng.gen_range_i64(1, 10_000) as i32;
        let max_total = (n + 1).min(200) as usize;
        let total = rng.gen_range_usize(1, max_total);
        let left_len = rng.gen_range_usize(0, total);
        let right_len = total - left_len;
        let left = random_vec(&mut rng, left_len, 0, n);
        let right = random_vec(&mut rng, right_len, 0, n);
        let (rn, rl, rr) = mutate(n, left, right, 0);
        emit(rn, rl, rr, &mut seen, &mut out, &mut count);
    }
}
