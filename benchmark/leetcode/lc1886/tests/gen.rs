use vstd::prelude::*;

verus! {

/// Build an n×n matrix filled with a constant binary value.
fn make_constant_matrix(n: usize, val: i32) -> (m: Vec<Vec<i32>>)
    requires
        1 <= n <= 10,
        val == 0 || val == 1,
    ensures
        m@.len() == n,
        forall|i: int| 0 <= i < n ==> (#[trigger] m@[i])@.len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==>
            (m@[i]@[j] == 0 || m@[i]@[j] == 1),
{
    let mut m: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 10,
            val == 0 || val == 1,
            m@.len() == i,
            forall|r: int| 0 <= r < i ==> (#[trigger] m@[r])@.len() == n,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                (m@[r]@[c] == 0 || m@[r]@[c] == 1),
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                val == 0 || val == 1,
                row@.len() == j,
                forall|c: int| 0 <= c < j ==> (row@[c] == 0 || row@[c] == 1),
            decreases n - j,
        {
            row.push(val);
            j += 1;
        }
        m.push(row);
        i += 1;
    }
    m
}

pub fn generate_test_case(
    mat: Vec<Vec<i32>>,
    target: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        1 <= mat@.len() <= 10,
        mat@.len() == target@.len(),
        forall|i: int| 0 <= i < mat@.len() ==> (#[trigger] mat@[i])@.len() == mat@.len(),
        forall|i: int| 0 <= i < target@.len() ==> (#[trigger] target@[i])@.len() == target@.len(),
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==>
            (mat@[i]@[j] == 0 || mat@[i]@[j] == 1),
        forall|i: int, j: int| 0 <= i < target@.len() && 0 <= j < target@.len() ==>
            (target@[i]@[j] == 0 || target@[i]@[j] == 1),
    ensures
        1 <= result.0@.len() <= 10,
        result.0@.len() == result.1@.len(),
        forall|i: int| 0 <= i < result.0@.len() ==> (#[trigger] result.0@[i])@.len() == result.0@.len(),
        forall|i: int| 0 <= i < result.1@.len() ==> (#[trigger] result.1@[i])@.len() == result.1@.len(),
        forall|i: int, j: int| 0 <= i < result.0@.len() && 0 <= j < result.0@.len() ==>
            (result.0@[i]@[j] == 0 || result.0@[i]@[j] == 1),
        forall|i: int, j: int| 0 <= i < result.1@.len() && 0 <= j < result.1@.len() ==>
            (result.1@[i]@[j] == 0 || result.1@[i]@[j] == 1),
{
    let n = mat.len();

    if mutation_kind == 0 {
        // identity
        (mat, target)
    } else if mutation_kind == 1 {
        // swap mat and target
        (target, mat)
    } else if mutation_kind == 2 {
        // flip mat[0][0]
        let mut new_row: Vec<i32> = Vec::new();
        let val0: i32 = if mat[0usize][0usize] == 0 { 1i32 } else { 0i32 };
        new_row.push(val0);
        let mut j: usize = 1;
        while j < n
            invariant
                1 <= j <= n,
                1 <= n <= 10,
                n == mat@.len(),
                new_row@.len() == j as int,
                mat@[0int]@.len() == n,
                forall|c: int| 0 <= c < j ==> (new_row@[c] == 0 || new_row@[c] == 1),
                forall|c: int| 0 <= c < n as int ==>
                    (mat@[0int]@[c] == 0 || mat@[0int]@[c] == 1),
            decreases n - j,
        {
            new_row.push(mat[0usize][j]);
            j += 1;
        }
        let mut m = mat;
        m.set(0, new_row);

        proof {
            // After set: m@.len() == old len, m@[0] == new_row, others unchanged
            assert(m@.len() == n);
            assert(m@[0int]@.len() == n);
            assert forall|i: int| 0 <= i < n implies (#[trigger] m@[i])@.len() == n by {
                if i == 0 {
                    assert(m@[0int]@.len() == n);
                } else {
                    // m@[i] unchanged from old mat
                }
            };
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies
                (m@[i]@[j] == 0 || m@[i]@[j] == 1) by {
                if i == 0 {
                    // from loop invariant on new_row
                } else {
                    // from original mat requires
                }
            };
        }

        (m, target)
    } else if mutation_kind == 3 {
        // flip target[0][0]
        let mut new_row: Vec<i32> = Vec::new();
        let val0: i32 = if target[0usize][0usize] == 0 { 1i32 } else { 0i32 };
        new_row.push(val0);
        let mut j: usize = 1;
        while j < n
            invariant
                1 <= j <= n,
                1 <= n <= 10,
                n == target@.len(),
                new_row@.len() == j as int,
                target@[0int]@.len() == n,
                forall|c: int| 0 <= c < j ==> (new_row@[c] == 0 || new_row@[c] == 1),
                forall|c: int| 0 <= c < n as int ==>
                    (target@[0int]@[c] == 0 || target@[0int]@[c] == 1),
            decreases n - j,
        {
            new_row.push(target[0usize][j]);
            j += 1;
        }
        let mut t = target;
        t.set(0, new_row);

        proof {
            assert(t@.len() == n);
            assert(t@[0int]@.len() == n);
            assert forall|i: int| 0 <= i < n implies (#[trigger] t@[i])@.len() == n by {
                if i == 0 {
                } else {
                }
            };
            assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n implies
                (t@[i]@[j] == 0 || t@[i]@[j] == 1) by {
                if i == 0 {
                } else {
                }
            };
        }

        (mat, t)
    } else if mutation_kind == 4 {
        // all-zero mat
        let m = make_constant_matrix(n, 0);
        assert(m@.len() == n);
        (m, target)
    } else if mutation_kind == 5 {
        // all-one mat
        let m = make_constant_matrix(n, 1);
        assert(m@.len() == n);
        (m, target)
    } else if mutation_kind == 6 {
        // all-zero target
        let t = make_constant_matrix(n, 0);
        assert(t@.len() == n);
        (mat, t)
    } else if mutation_kind == 7 {
        // all-one target
        let t = make_constant_matrix(n, 1);
        assert(t@.len() == n);
        (mat, t)
    } else {
        // fallback: identity
        (mat, target)
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
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_binary_matrix(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(n);
    for _ in 0..n {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_usize(0, 1) as i32);
        }
        mat.push(row);
    }
    mat
}

fn mutate(mat: Vec<Vec<i32>>, target: Vec<Vec<i32>>, mk: u8) -> (Vec<Vec<i32>>, Vec<Vec<i32>>) {
    generate_test_case(mat, target, mk)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1886);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, target: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}|{:?}", mat, target);
        if !seen.insert(key) { return; }
        let output = Solution::find_rotation(mat.clone(), target.clone());
        writeln!(out, "{}", json!({
            "input": {"mat": mat, "target": target},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<Vec<i32>>, Vec<Vec<i32>>)> = vec![
        (vec![vec![0,1],vec![1,0]], vec![vec![1,0],vec![0,1]]),
        (vec![vec![0,1],vec![1,1]], vec![vec![1,0],vec![0,1]]),
        (vec![vec![0,0,0],vec![0,1,0],vec![1,1,1]], vec![vec![1,1,1],vec![0,1,0],vec![0,0,0]]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every example
    for (m, t) in &examples {
        for &mk in &mutation_kinds {
            let (rm, rt) = mutate(m.clone(), t.clone(), mk);
            emit(rm, rt, &mut seen, &mut out, &mut total);
        }
    }

    // Structured seeds: identity matrices, all-zero, all-one, checkerboard
    for n in 1..=5usize {
        // All-zero
        let z = vec![vec![0i32; n]; n];
        // All-one
        let o = vec![vec![1i32; n]; n];
        // Checkerboard
        let mut cb = vec![vec![0i32; n]; n];
        for i in 0..n { for j in 0..n { cb[i][j] = ((i + j) % 2) as i32; } }

        for &mk in &mutation_kinds {
            let (rm, rt) = mutate(z.clone(), o.clone(), mk);
            emit(rm, rt, &mut seen, &mut out, &mut total);
            let (rm, rt) = mutate(cb.clone(), cb.clone(), mk);
            emit(rm, rt, &mut seen, &mut out, &mut total);
        }
    }

    // Random matrices across size classes
    let sizes: Vec<usize> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let mut _attempts_0 = 0usize;
    while total < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let n = sizes[rng.gen_range_usize(0, sizes.len() - 1)];
        let mat = random_binary_matrix(&mut rng, n);
        let target = random_binary_matrix(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (rm, rt) = mutate(mat, target, mk);
        emit(rm, rt, &mut seen, &mut out, &mut total);
    }
}
