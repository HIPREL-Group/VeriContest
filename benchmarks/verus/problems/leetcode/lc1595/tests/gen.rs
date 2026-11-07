use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    cost: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= cost.len() <= 12,
        forall|i: int| 0 <= i < cost.len() ==> (#[trigger] cost[i]).len() == cost[0].len(),
        1 <= cost[0].len() <= 12,
        cost.len() >= cost[0].len(),
        forall|i: int, j: int|
            #![trigger cost[i][j]]
            0 <= i < cost.len() && 0 <= j < cost[0].len()
                ==> 0 <= cost[i][j] <= 100,
    ensures
        1 <= result.len() <= 12,
        forall|i: int|
            0 <= i < result.len() ==> (#[trigger] result[i])@.len() == result[0]@.len(),
        1 <= result[0]@.len() <= 12,
        result.len() >= result[0]@.len(),
        forall|i: int, j: int|
            #![trigger result[i]@[j]]
            0 <= i < result.len() && 0 <= j < result[0]@.len()
                ==> 0 <= result[i]@[j] <= 100,
{
    let rows = cost.len();
    let cols = cost[0].len();

    if mutation_kind == 0 {
        // identity
        cost
    } else if mutation_kind == 1 || mutation_kind == 2 {
        // all-0 (mutation 1) or all-100 (mutation 2) matrix of same dimensions
        let fill: i32 = if mutation_kind == 1 { 0 } else { 100 };
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 12,
                1 <= cols <= 12,
                rows >= cols,
                fill == 0 || fill == 100,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r])@.len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 0 <= #[trigger] res[r]@[c] && res[r]@[c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 12,
                    fill == 0 || fill == 100,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int
                        ==> 0 <= #[trigger] row[c] && row[c] <= 100,
                decreases cols - j,
            {
                row.push(fill);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else if mutation_kind == 3 {
        // set all values to 50 (mid-range)
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 12,
                1 <= cols <= 12,
                rows >= cols,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r])@.len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 0 <= #[trigger] res[r]@[c] && res[r]@[c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 12,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int
                        ==> 0 <= #[trigger] row[c] && row[c] <= 100,
                decreases cols - j,
            {
                row.push(50);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else if mutation_kind == 4 {
        // set all values to 1 (low uniform cost)
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 12,
                1 <= cols <= 12,
                rows >= cols,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r])@.len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 0 <= #[trigger] res[r]@[c] && res[r]@[c] <= 100,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 12,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int
                        ==> 0 <= #[trigger] row[c] && row[c] <= 100,
                decreases cols - j,
            {
                row.push(1);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else {
        // fallback: identity
        cost
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_cost_matrix(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_usize(0, 100) as i32);
        }
        mat.push(row);
    }
    mat
}

fn all_val_matrix(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        mat.push(vec![val; n]);
    }
    mat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1595);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |cost: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", cost);
        if !seen.insert(key) { return; }
        let output = Solution::connect_two_groups(cost.clone());
        writeln!(out, "{}", json!({"input": {"cost": cost}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex1 = vec![vec![15, 96], vec![36, 2]];
    let ex2 = vec![vec![1, 3, 5], vec![4, 1, 1], vec![1, 5, 3]];
    let ex3 = vec![vec![2, 5, 1], vec![3, 4, 7], vec![8, 1, 2], vec![6, 2, 4], vec![3, 8, 8]];
    emit(ex1, &mut seen, &mut out, &mut count);
    emit(ex2, &mut seen, &mut out, &mut count);
    emit(ex3, &mut seen, &mut out, &mut count);

    // Structured seed matrices with all mutation kinds
    let seed_matrices: Vec<Vec<Vec<i32>>> = vec![
        // 1x1
        vec![vec![0]],
        vec![vec![50]],
        vec![vec![100]],
        // 2x1
        vec![vec![0], vec![100]],
        vec![vec![50], vec![50]],
        // 2x2
        vec![vec![1, 2], vec![3, 4]],
        vec![vec![0, 0], vec![0, 0]],
        vec![vec![100, 100], vec![100, 100]],
        vec![vec![0, 100], vec![100, 0]],
        // 3x2
        vec![vec![1, 2], vec![3, 4], vec![5, 6]],
        // 3x3
        vec![vec![1, 1, 1], vec![1, 1, 1], vec![1, 1, 1]],
        all_val_matrix(3, 3, 0),
        all_val_matrix(3, 3, 100),
        // 4x3
        vec![vec![10, 20, 30], vec![40, 50, 60], vec![70, 80, 90], vec![1, 2, 3]],
        // Square at boundary sizes
        all_val_matrix(4, 4, 50),
        all_val_matrix(6, 6, 25),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for mat in &seed_matrices {
        for &mk in &mutation_kinds {
            let result = generate_test_case(mat.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random matrices across size classes (m >= n always)
    let mut _attempts_0 = 0usize;
    while count < target_count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let (m, n) = match count % 6 {
            0 => (1, 1),
            1 => {
                let nn = rng.gen_range_usize(1, 2);
                let mm = rng.gen_range_usize(nn, 3);
                (mm, nn)
            },
            2 => {
                let nn = rng.gen_range_usize(1, 4);
                let mm = rng.gen_range_usize(nn, 6);
                (mm, nn)
            },
            3 => {
                let nn = rng.gen_range_usize(2, 6);
                let mm = rng.gen_range_usize(nn, 8);
                (mm, nn)
            },
            4 => {
                let nn = rng.gen_range_usize(3, 8);
                let mm = rng.gen_range_usize(nn, 10);
                (mm, nn)
            },
            _ => {
                let nn = rng.gen_range_usize(4, 12);
                let mm = rng.gen_range_usize(nn, 12);
                (mm, nn)
            },
        };

        let mat = if count % 15 == 0 {
            all_val_matrix(m, n, 0)
        } else if count % 15 == 5 {
            all_val_matrix(m, n, 100)
        } else {
            random_cost_matrix(&mut rng, m, n)
        };

        let mk = rng.gen_range_usize(0, 4) as u8;
        let result = generate_test_case(mat, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
