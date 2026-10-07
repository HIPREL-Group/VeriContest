use vstd::prelude::*;

verus! {

fn generate_shrink(seats: Vec<i32>) -> (result: Vec<i32>)
    requires
        seats.len() > 2,
        forall|i: int| 0 <= i < seats.len() ==> 0 <= #[trigger] seats[i] <= 1,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 0,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 1,
    ensures
        2 <= result.len() <= seats.len() as int,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1,
        exists|i: int| 0 <= i < result.len() && result[i] == 0,
        exists|i: int| 0 <= i < result.len() && result[i] == 1,
{
    let mut s = seats;
    let last = s.len() - 1;
    let popped_val = s[last];
    let mut dup_witness: usize = 0;
    let mut has_dup = false;
    let mut k: usize = 0;
    while k < last
        invariant
            0 <= k <= last,
            last == s.len() - 1,
            s@ == seats@,
            has_dup ==> 0 <= dup_witness < k && s[dup_witness as int] == popped_val,
        decreases last - k,
    {
        if s[k] == popped_val && !has_dup { has_dup = true; dup_witness = k; }
        k += 1;
    }
    if has_dup {
        proof { assert(popped_val == 0 || popped_val == 1); }
        s.pop();
        proof {
            assert(dup_witness < s.len());
            assert(s[dup_witness as int] == popped_val);
            if popped_val == 0 {
                assert(s[dup_witness as int] == 0);
                let w1 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 1;
                assert(seats[w1] == 1);
                assert(seats[last as int] == 0);
                assert(w1 != last as int);
                assert(w1 < s@.len() as int);
                assert(s[w1] == 1);
            } else {
                assert(s[dup_witness as int] == 1);
                let w0 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 0;
                assert(seats[w0] == 0);
                assert(seats[last as int] == 1);
                assert(w0 != last as int);
                assert(w0 < s@.len() as int);
                assert(s[w0] == 0);
            }
        }
        s
    } else { s }
}

pub fn generate_test_case(seats: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= seats.len() <= 20_000,
        forall|i: int| 0 <= i < seats.len() ==> 0 <= #[trigger] seats[i] <= 1,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 0,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 1,
    ensures
        2 <= result.len() <= 20_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1,
        exists|i: int| 0 <= i < result.len() && result[i] == 0,
        exists|i: int| 0 <= i < result.len() && result[i] == 1,
{
    if mutation_kind == 1 && seats.len() < 20_000 {
        // grow: append 0
        let mut s = seats;
        s.push(0);
        proof {
            let orig_len: int = seats@.len() as int;
            assert(s[orig_len] == 0);
            let w1 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 1;
            assert(s[w1] == 1);
        }
        s
    } else if mutation_kind == 2 && seats.len() < 20_000 {
        // grow: append 1
        let mut s = seats;
        s.push(1);
        proof {
            let orig_len: int = seats@.len() as int;
            assert(s[orig_len] == 1);
            let w0 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 0;
            assert(s[w0] == 0);
        }
        s
    } else if mutation_kind == 3 {
        // swap elements 0 and 1
        let mut s = seats;
        let a = s[0];
        let b = s[1];
        s.set(0, b);
        s.set(1, a);
        proof {
            let w0 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 0;
            let w1 = choose|i: int| 0 <= i < seats@.len() && seats[i] == 1;
            if w0 == 0 { assert(s[1int] == 0); }
            else if w0 == 1 { assert(s[0int] == 0); }
            else { assert(s[w0] == 0); }
            if w1 == 0 { assert(s[1int] == 1); }
            else if w1 == 1 { assert(s[0int] == 1); }
            else { assert(s[w1] == 1); }
        }
        s
    } else if mutation_kind == 4 {
        // set index 0 to 0 if there's a 1 elsewhere
        let mut s = seats;
        let mut witness: usize = 0;
        let mut found = false;
        let mut k: usize = 1;
        while k < s.len()
            invariant
                1 <= k <= s.len(),
                s@ == seats@,
                found ==> 1 <= witness < k && s[witness as int] == 1,
            decreases s.len() - k,
        {
            if s[k] == 1 && !found { found = true; witness = k; }
            k += 1;
        }
        if found {
            s.set(0, 0);
            proof {
                assert(s[0int] == 0);
                assert(s[witness as int] == 1);
            }
            s
        } else { s }
    } else if mutation_kind == 5 {
        // set index 0 to 1 if there's a 0 elsewhere
        let mut s = seats;
        let mut witness: usize = 0;
        let mut found = false;
        let mut k: usize = 1;
        while k < s.len()
            invariant
                1 <= k <= s.len(),
                s@ == seats@,
                found ==> 1 <= witness < k && s[witness as int] == 0,
            decreases s.len() - k,
        {
            if s[k] == 0 && !found { found = true; witness = k; }
            k += 1;
        }
        if found {
            s.set(0, 1);
            proof {
                assert(s[0int] == 1);
                assert(s[witness as int] == 0);
            }
            s
        } else { s }
    } else if mutation_kind == 6 && seats.len() > 2 {
        // shrink: pop last if safe
        generate_shrink(seats)
    } else {
        // identity / fallback
        seats
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(seats: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(seats, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_seats(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut seats = Vec::with_capacity(len);
    for _ in 0..len {
        seats.push(rng.gen_range_usize(0, 1) as i32);
    }
    let has_zero = seats.iter().any(|&x| x == 0);
    let has_one = seats.iter().any(|&x| x == 1);
    if !has_zero {
        let idx = rng.gen_range_usize(0, len - 1);
        seats[idx] = 0;
    }
    if !has_one {
        let mut idx = rng.gen_range_usize(0, len - 1);
        if seats[idx] == 0 && len > 1 {
            idx = (idx + 1) % len;
        }
        seats[idx] = 1;
        if !seats.iter().any(|&x| x == 0) {
            let fix = (idx + 1) % len;
            seats[fix] = 0;
        }
    }
    seats
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(849);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |seats: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", seats);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_dist_to_closest(seats.clone());
        writeln!(out, "{}", json!({"input": {"seats": seats}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 0, 0, 1, 0, 1],
        vec![1, 0, 0, 0],
        vec![0, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds covering edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 0],
        vec![0, 1],
        vec![1, 0, 1],
        vec![0, 0, 1],
        vec![1, 0, 0],
        vec![0, 1, 0],
        vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        vec![0, 0, 0, 0, 1],
        vec![1, 0, 0, 0, 0],
        vec![1, 1, 0, 1, 1],
        vec![0, 0, 0, 1, 0, 0, 0],
        vec![1, 0, 1, 0, 1, 0, 1],
        vec![0, 1, 0, 1, 0, 1, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..80 {
        if count >= count_target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 20_000),
        };
        let s = random_seats(&mut rng, n);
        let mk = rng.gen_range_usize(0, 6) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity mutations
    while count < count_target {
        let n = rng.gen_range_usize(2, 20_000);
        let s = random_seats(&mut rng, n);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
