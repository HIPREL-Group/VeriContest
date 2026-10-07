use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<Vec<i32>>` of bookings (each a 3-element vec
/// [first, last, seats]) from parallel arrays of firsts, lasts, and seats,
/// applying mutation_kind to diversify the generated inputs.
pub fn generate_test_case(
    firsts: &Vec<i32>,
    lasts: &Vec<i32>,
    seats: &Vec<i32>,
    n: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= n <= 20_000,
        1 <= firsts.len() <= 20_000,
        firsts.len() == lasts.len(),
        firsts.len() == seats.len(),
        forall |i: int| 0 <= i < firsts.len() ==> 1 <= #[trigger] firsts[i] <= lasts[i] <= n,
        forall |i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 10_000,
    ensures
        1 <= result.1 <= 20_000,
        1 <= result.0.len() <= 20_000,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i]@.len() == 3,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= result.0[i][1] <= result.1,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][2] <= 10_000,
{
    let mut bookings: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < firsts.len()
        invariant
            0 <= k <= firsts.len(),
            1 <= n <= 20_000,
            firsts.len() == lasts.len(),
            firsts.len() == seats.len(),
            1 <= firsts.len() <= 20_000,
            bookings.len() == k,
            forall |i: int| 0 <= i < firsts.len() ==> 1 <= #[trigger] firsts[i] <= lasts[i] <= n,
            forall |i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 10_000,
            forall |j: int| 0 <= j < k ==> #[trigger] bookings[j]@.len() == 3,
            forall |j: int| 0 <= j < k ==> 1 <= #[trigger] bookings[j][0] <= bookings[j][1] <= n,
            forall |j: int| 0 <= j < k ==> 1 <= #[trigger] bookings[j][2] <= 10_000,
        decreases firsts.len() - k,
    {
        // Mutation 0: normal
        // Mutation 1: all seats = 1
        // Mutation 2: all seats = 10_000
        // Mutation 3: single flight (last = first)
        // Mutation 4: full range (first = 1, last = n)
        // Mutation 5: first flight only (first = 1, last = 1)
        let first_val: i32 = if mutation_kind == 4 || mutation_kind == 5 {
            1i32
        } else {
            firsts[k]
        };
        let last_val: i32 = if mutation_kind == 3 {
            firsts[k]
        } else if mutation_kind == 4 {
            n
        } else if mutation_kind == 5 {
            1i32
        } else {
            lasts[k]
        };
        let seat_val: i32 = if mutation_kind == 1 {
            1i32
        } else if mutation_kind == 2 {
            10_000i32
        } else {
            seats[k]
        };

        assert(1 <= first_val <= last_val <= n);
        assert(1 <= seat_val <= 10_000);

        let mut b: Vec<i32> = Vec::new();
        b.push(first_val);
        b.push(last_val);
        b.push(seat_val);

        assert(b@.len() == 3);
        assert(b[0] == first_val);
        assert(b[1] == last_val);
        assert(b[2] == seat_val);

        bookings.push(b);
        k = k + 1;
    }

    (bookings, n)
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

fn random_bookings(rng: &mut Rng, n: i32, num_bookings: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut firsts = Vec::with_capacity(num_bookings);
    let mut lasts = Vec::with_capacity(num_bookings);
    let mut seats_vec = Vec::with_capacity(num_bookings);
    for _ in 0..num_bookings {
        let f = rng.gen_range_i64(1, n as i64) as i32;
        let l = rng.gen_range_i64(f as i64, n as i64) as i32;
        let s = rng.gen_range_i64(1, 10_000) as i32;
        firsts.push(f);
        lasts.push(l);
        seats_vec.push(s);
    }
    (firsts, lasts, seats_vec)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1109);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |bookings_vec: Vec<Vec<i32>>, n: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?},{}", bookings_vec, n);
        if !seen.insert(key) { return; }
        let result = Solution::corp_flight_bookings(bookings_vec.clone(), n);
        writeln!(out, "{}", json!({
            "input": {"bookings": bookings_vec, "n": n},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example 1: bookings = [[1,2,10],[2,3,20],[2,5,25]], n = 5
    {
        let firsts = vec![1, 2, 2];
        let lasts = vec![2, 3, 5];
        let seats_v = vec![10, 20, 25];
        for mk in 0u8..=5 {
            let (bk, nn) = generate_test_case(&firsts, &lasts, &seats_v, 5, mk);
            emit(bk, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: bookings = [[1,2,10],[2,2,15]], n = 2
    {
        let firsts = vec![1, 2];
        let lasts = vec![2, 2];
        let seats_v = vec![10, 15];
        for mk in 0u8..=5 {
            let (bk, nn) = generate_test_case(&firsts, &lasts, &seats_v, 2, mk);
            emit(bk, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single booking, single flight
    {
        let firsts = vec![1];
        let lasts = vec![1];
        let seats_v = vec![1];
        for mk in 0u8..=5 {
            let (bk, nn) = generate_test_case(&firsts, &lasts, &seats_v, 1, mk);
            emit(bk, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single booking covering all flights, max seats
    {
        let firsts = vec![1];
        let lasts = vec![100];
        let seats_v = vec![10_000];
        for mk in 0u8..=5 {
            let (bk, nn) = generate_test_case(&firsts, &lasts, &seats_v, 100, mk);
            emit(bk, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];
    while count < target_count {
        // Size class for n
        let n: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 20) as i32,       // small
            2 => rng.gen_range_i64(21, 200) as i32,     // medium
            3 => rng.gen_range_i64(201, 2000) as i32,   // large
            _ => rng.gen_range_i64(2001, 20000) as i32, // max
        };

        // Size class for number of bookings
        let nb: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 500),     // large
            _ => rng.gen_range_usize(501, 2000),    // max
        };

        let (firsts, lasts, seats_v) = random_bookings(&mut rng, n, nb);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (bk, nn) = generate_test_case(&firsts, &lasts, &seats_v, n, mk);
        emit(bk, nn, &mut seen, &mut out, &mut count);
    }
}
