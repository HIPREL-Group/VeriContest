use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seats: Vec<i32>,
    students: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= seats.len() <= 100,
        students.len() == seats.len(),
        seats@.len() <= 100,
        students@.len() == seats@.len(),
        forall|i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 100,
        forall|i: int| 0 <= i < students.len() ==> 1 <= #[trigger] students[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        result.1.len() == result.0.len(),
        result.0@.len() <= 100,
        result.1@.len() == result.0@.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (seats, students)
    } else if mutation_kind == 1 {
        // set first seat to min boundary
        let mut s = seats;
        s.set(0, 1);
        (s, students)
    } else if mutation_kind == 2 {
        // set first seat to max boundary
        let mut s = seats;
        s.set(0, 100);
        (s, students)
    } else if mutation_kind == 3 {
        // set first student to min boundary
        let mut st = students;
        st.set(0, 1);
        (seats, st)
    } else if mutation_kind == 4 {
        // set first student to max boundary
        let mut st = students;
        st.set(0, 100);
        (seats, st)
    } else if mutation_kind == 5 {
        // swap first seat and student values
        let v0 = seats[0];
        let v1 = students[0];
        let mut s = seats;
        let mut st = students;
        s.set(0, v1);
        st.set(0, v0);
        (s, st)
    } else if mutation_kind == 6 && seats[0] < 100 {
        // nudge first seat up
        let new_val = seats[0] + 1;
        let mut s = seats;
        s.set(0, new_val);
        (s, students)
    } else if mutation_kind == 7 && students[0] > 1 {
        // nudge first student down
        let new_val = students[0] - 1;
        let mut st = students;
        st.set(0, new_val);
        (seats, st)
    } else if mutation_kind == 8 {
        // set last seat to min boundary
        let last = seats.len() - 1;
        let mut s = seats;
        s.set(last, 1);
        (s, students)
    } else if mutation_kind == 9 {
        // set last student to max boundary
        let last = students.len() - 1;
        let mut st = students;
        st.set(last, 100);
        (seats, st)
    } else {
        // fallback: identity
        (seats, students)
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100) as i32);
    }
    arr
}

fn mutate(seats: Vec<i32>, students: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(seats, students, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2037);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |seats: Vec<i32>, students: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}|{:?}", seats, students);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_moves_to_seat(seats.clone(), students.clone());
        writeln!(out, "{}", json!({
            "input": {"seats": seats, "students": students},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![3, 1, 5], vec![2, 7, 4]),
        (vec![4, 1, 5, 9], vec![1, 3, 2, 6]),
        (vec![2, 2, 6, 6], vec![1, 3, 2, 6]),
    ];

    for (s, st) in &examples {
        emit(s.clone(), st.clone(), &mut seen, &mut out, &mut emitted);
    }

    // Seed inputs for mutation
    let seed_inputs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![100], vec![100]),
        (vec![1], vec![100]),
        (vec![100], vec![1]),
        (vec![50, 50], vec![50, 50]),
        (vec![1, 100], vec![100, 1]),
        (vec![1, 1, 1], vec![100, 100, 100]),
        (vec![50], vec![1]),
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
        (vec![10, 20, 30], vec![10, 20, 30]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for (s, st) in &seed_inputs {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let (rs, rst) = mutate(s.clone(), st.clone(), mk);
            emit(rs, rst, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random inputs with diverse size classes and mutations
    while emitted < count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,                                       // minimal
            1 => rng.gen_range_usize(1, 5),               // tiny
            2 => rng.gen_range_usize(6, 20),              // small
            3 => rng.gen_range_usize(21, 60),             // medium
            _ => rng.gen_range_usize(61, 100),            // large
        };
        let seats = random_array(&mut rng, n);
        let students = random_array(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (rs, rst) = mutate(seats, students, mk);
        emit(rs, rst, &mut seen, &mut out, &mut emitted);
    }
}
