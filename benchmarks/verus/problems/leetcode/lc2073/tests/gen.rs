use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    tickets: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= tickets.len() <= 100,
        0 <= k < tickets.len(),
        forall|j: int| 0 <= j < tickets.len() ==> 1 <= #[trigger] tickets[j] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        0 <= result.1 < result.0.len(),
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (tickets, k)
    } else if mutation_kind == 1 {
        // set element at k to 1 (minimum ticket count)
        let mut t = tickets;
        t.set(k as usize, 1);
        (t, k)
    } else if mutation_kind == 2 {
        // set element at k to 100 (maximum ticket count)
        let mut t = tickets;
        t.set(k as usize, 100);
        (t, k)
    } else if mutation_kind == 3 {
        // set all elements to tickets[k] (uniform queue)
        let val = tickets[k as usize];
        let mut t = tickets;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == tickets.len(),
                1 <= t.len() <= 100,
                1 <= val <= 100,
                0 <= k < t.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] t[j] == val,
                forall|j: int| i <= j < t.len() ==> #[trigger] t[j] == tickets[j],
                forall|j: int| 0 <= j < t.len() ==> 1 <= #[trigger] t[j] <= 100,
            decreases t.len() - i,
        {
            t.set(i, val);
            i += 1;
        }
        (t, k)
    } else if mutation_kind == 4 && tickets.len() < 100 {
        // grow: push element with value 1 at end
        let mut t = tickets;
        t.push(1);
        (t, k)
    } else if mutation_kind == 5 && tickets.len() > 1 && k < tickets.len() as i32 - 1 {
        // shrink: pop last element (only if k is not the last index)
        let mut t = tickets;
        t.pop();
        (t, k)
    } else if mutation_kind == 6 {
        // set all elements to 1
        let mut t = tickets;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == tickets.len(),
                1 <= t.len() <= 100,
                0 <= k < t.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] t[j] == 1i32,
                forall|j: int| i <= j < t.len() ==> #[trigger] t[j] == tickets[j],
                forall|j: int| 0 <= j < t.len() ==> 1 <= #[trigger] t[j] <= 100,
            decreases t.len() - i,
        {
            t.set(i, 1);
            i += 1;
        }
        (t, k)
    } else if mutation_kind == 7 {
        // nudge tickets[k] up by 1 if < 100
        let mut t = tickets;
        if t[k as usize] < 100 {
            t.set(k as usize, t[k as usize] + 1);
        }
        (t, k)
    } else if mutation_kind == 8 {
        // nudge tickets[k] down by 1 if > 1
        let mut t = tickets;
        if t[k as usize] > 1 {
            t.set(k as usize, t[k as usize] - 1);
        }
        (t, k)
    } else if mutation_kind == 9 && tickets.len() >= 2 {
        // swap tickets[0] and tickets[last]
        let mut t = tickets;
        let last = t.len() - 1;
        let v0 = t[0];
        let vl = t[last];
        t.set(0, vl);
        t.set(last, v0);
        (t, k)
    } else if mutation_kind == 10 {
        // move k to 0
        (tickets, 0)
    } else if mutation_kind == 11 {
        // move k to last index
        let last_idx = (tickets.len() - 1) as i32;
        (tickets, last_idx)
    } else {
        // fallback: identity
        (tickets, k)
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

fn mutate(tickets: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(tickets, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_tickets(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut tickets = Vec::with_capacity(len);
    for _ in 0..len {
        tickets.push(rng.gen_range_i64(1, 100) as i32);
    }
    tickets
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2073);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |tickets: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", tickets, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::time_required_to_buy(tickets.clone(), k);
        writeln!(out, "{}", json!({"input": {"tickets": tickets, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![2, 3, 2], 2, &mut seen, &mut out, &mut count);
    emit(vec![5, 1, 1, 1], 0, &mut seen, &mut out, &mut count);

    // Seed pool: interesting ticket configurations
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 0),
        (vec![100], 0),
        (vec![1, 1], 0),
        (vec![1, 1], 1),
        (vec![100, 100], 0),
        (vec![100, 100], 1),
        (vec![1, 100], 0),
        (vec![1, 100], 1),
        (vec![100, 1], 0),
        (vec![100, 1], 1),
        (vec![1, 2, 3, 4, 5], 2),
        (vec![5, 4, 3, 2, 1], 2),
        (vec![3, 3, 3, 3, 3], 2),
        (vec![1, 1, 1, 1, 1], 4),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for (tickets, k) in &seeds {
        for &mk in &mutation_kinds {
            let (t, k2) = mutate(tickets.clone(), *k, mk);
            emit(t, k2, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),      // tiny
        (4, 10),     // small
        (11, 30),    // medium
        (31, 60),    // large
        (61, 100),   // max
    ];

    for _ in 0..80 {
        if count >= target_count { break; }
        let (lo, hi) = size_classes[rng.gen_range_usize(0, size_classes.len() - 1)];
        let n = rng.gen_range_usize(lo, hi);
        let tickets = random_tickets(&mut rng, n);
        let k = rng.gen_range_usize(0, n - 1) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (t, k2) = mutate(tickets, k, mk);
        emit(t, k2, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutations on random inputs
    while count < target_count {
        let n = rng.gen_range_usize(1, 100);
        let tickets = random_tickets(&mut rng, n);
        let k = rng.gen_range_usize(0, n - 1) as i32;
        let (t, k2) = mutate(tickets, k, 0);
        emit(t, k2, &mut seen, &mut out, &mut count);
    }
}
