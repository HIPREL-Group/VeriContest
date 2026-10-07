use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    students: Vec<i32>,
    sandwiches: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        students.len() == sandwiches.len(),
        1 <= students.len() <= 100,
        forall|i: int| 0 <= i < students.len() ==> students[i] == 0 || students[i] == 1,
        forall|i: int| 0 <= i < sandwiches.len() ==> sandwiches[i] == 0 || sandwiches[i] == 1,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> result.0[i] == 0 || result.0[i] == 1,
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i] == 0 || result.1[i] == 1,
{
    if mutation_kind == 0 {
        // identity
        (students, sandwiches)
    } else if mutation_kind == 1 {
        // flip first student preference (0↔1)
        let mut s = students;
        if s[0] == 0 {
            s.set(0, 1);
        } else {
            s.set(0, 0);
        }
        (s, sandwiches)
    } else if mutation_kind == 2 {
        // flip first sandwich type (0↔1)
        let mut w = sandwiches;
        if w[0] == 0 {
            w.set(0, 1);
        } else {
            w.set(0, 0);
        }
        (students, w)
    } else if mutation_kind == 3 {
        // set all students to 0
        let n = students.len();
        let mut s: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                n == students.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> s[j] == 0,
            decreases n - i,
        {
            s.push(0);
            i += 1;
        }
        (s, sandwiches)
    } else if mutation_kind == 4 {
        // set all students to 1
        let n = students.len();
        let mut s: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == i,
                n == students.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> s[j] == 1,
            decreases n - i,
        {
            s.push(1);
            i += 1;
        }
        (s, sandwiches)
    } else if mutation_kind == 5 {
        // set all sandwiches to 0
        let n = sandwiches.len();
        let mut w: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                w.len() == i,
                n == sandwiches.len(),
                n == students.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> w[j] == 0,
            decreases n - i,
        {
            w.push(0);
            i += 1;
        }
        (students, w)
    } else if mutation_kind == 6 {
        // set all sandwiches to 1
        let n = sandwiches.len();
        let mut w: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                w.len() == i,
                n == sandwiches.len(),
                n == students.len(),
                1 <= n <= 100,
                forall|j: int| 0 <= j < i as int ==> w[j] == 1,
            decreases n - i,
        {
            w.push(1);
            i += 1;
        }
        (students, w)
    } else if mutation_kind == 7 && students.len() >= 2 {
        // swap first two students
        let mut s = students;
        let a = s[0];
        let b = s[1];
        s.set(0, b);
        s.set(1, a);
        (s, sandwiches)
    } else if mutation_kind == 8 && sandwiches.len() >= 2 {
        // swap first two sandwiches
        let mut w = sandwiches;
        let a = w[0];
        let b = w[1];
        w.set(0, b);
        w.set(1, a);
        (students, w)
    } else if mutation_kind == 9 {
        // flip last student preference
        let mut s = students;
        let last = s.len() - 1;
        if s[last] == 0 {
            s.set(last, 1);
        } else {
            s.set(last, 0);
        }
        (s, sandwiches)
    } else {
        // fallback: identity
        (students, sandwiches)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_binary_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_usize(0, 1) as i32);
    }
    v
}

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
    let mut generated: usize = 0;

    // Example 1: students = [1,1,0,0], sandwiches = [0,1,0,1] -> 0
    {
        let students = vec![1, 1, 0, 0];
        let sandwiches = vec![0, 1, 0, 1];
        let result = Solution::count_students(students.clone(), sandwiches.clone());
        writeln!(out, "{}", json!({
            "input": {"students": students, "sandwiches": sandwiches},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Example 2: students = [1,1,1,0,0,1], sandwiches = [1,0,0,0,1,1] -> 3
    {
        let students = vec![1, 1, 1, 0, 0, 1];
        let sandwiches = vec![1, 0, 0, 0, 1, 1];
        let result = Solution::count_students(students.clone(), sandwiches.clone());
        writeln!(out, "{}", json!({
            "input": {"students": students, "sandwiches": sandwiches},
            "output": result
        })).unwrap();
        generated += 1;
    }

    let num_mutations: u8 = 10;

    while generated < count {
        // Size classes for array length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };

        let students = random_binary_vec(&mut rng, n);
        let sandwiches = random_binary_vec(&mut rng, n);

        let mutation = (rng.gen_range_usize(0, num_mutations as usize - 1)) as u8;

        let (s, w) = generate_test_case(students, sandwiches, mutation);
        let result = Solution::count_students(s.clone(), w.clone());

        writeln!(out, "{}", json!({
            "input": {"students": s, "sandwiches": w},
            "output": result
        })).unwrap();

        generated += 1;
    }
}
