use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    rows: &Vec<i32>,
    cols: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<Vec<i32>>))
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        1 <= rows.len() <= 100,
        rows.len() == cols.len(),
        forall|k: int| 0 <= k < rows.len() ==> 0 <= #[trigger] rows[k] < m,
        forall|k: int| 0 <= k < cols.len() ==> 0 <= #[trigger] cols[k] < n,
    ensures
        1 <= result.0 <= 50,
        1 <= result.1 <= 50,
        1 <= result.2.len() <= 100,
        forall|k: int|
            0 <= k < result.2.len() ==> (#[trigger] result.2.deep_view()[k]).len() == 2,
        forall|k: int|
            0 <= k < result.2.len() ==> 0 <= (#[trigger] result.2.deep_view()[k])[0]
                < result.0,
        forall|k: int|
            0 <= k < result.2.len() ==> 0 <= (#[trigger] result.2.deep_view()[k])[1]
                < result.1,
{
    let m_out: i32 = if mutation_kind == 1 && m < 50 {
        (m + 1) as i32
    } else if mutation_kind == 2 {
        50i32
    } else if mutation_kind == 3 {
        50i32
    } else {
        m
    };
    let n_out: i32 = if mutation_kind == 4 && n < 50 {
        (n + 1) as i32
    } else if mutation_kind == 5 {
        50i32
    } else if mutation_kind == 3 {
        50i32
    } else {
        n
    };

    // Build indices Vec<Vec<i32>> from parallel rows/cols arrays
    let mut indices: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            0 <= i <= rows.len(),
            indices.len() == i as nat,
            rows.len() == cols.len(),
            1 <= rows.len() <= 100,
            1 <= m <= 50,
            1 <= n <= 50,
            m <= m_out,
            n <= n_out,
            1 <= m_out <= 50,
            1 <= n_out <= 50,
            forall|k: int| 0 <= k < rows.len() ==> 0 <= #[trigger] rows[k] < m,
            forall|k: int| 0 <= k < cols.len() ==> 0 <= #[trigger] cols[k] < n,
            forall|k: int|
                0 <= k < i as int ==> (#[trigger] indices.deep_view()[k]).len() == 2,
            forall|k: int|
                0 <= k < i as int ==> 0 <= (#[trigger] indices.deep_view()[k])[0] < m_out,
            forall|k: int|
                0 <= k < i as int ==> 0 <= (#[trigger] indices.deep_view()[k])[1] < n_out,
        decreases rows.len() - i,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(rows[i]);
        pair.push(cols[i]);

        assert(pair@.len() == 2);
        assert(pair@[0] == rows[i as int]);
        assert(pair@[1] == cols[i as int]);

        let ghost old_indices_dv = indices.deep_view();
        indices.push(pair);

        proof {
            assert(indices.deep_view()[i as int] =~= indices@[i as int]@);
            assert forall|k: int|
                0 <= k < i as int + 1
                implies (#[trigger] indices.deep_view()[k]).len() == 2
            by {
                if k < i as int {
                    assert(indices.deep_view()[k] =~= old_indices_dv[k]);
                } else {
                    assert(indices.deep_view()[k].len() == 2);
                }
            }
            assert forall|k: int|
                0 <= k < i as int + 1
                implies 0 <= (#[trigger] indices.deep_view()[k])[0] < m_out
            by {
                if k < i as int {
                    assert(indices.deep_view()[k] =~= old_indices_dv[k]);
                } else {
                    assert(indices.deep_view()[k][0] == rows[i as int]);
                }
            }
            assert forall|k: int|
                0 <= k < i as int + 1
                implies 0 <= (#[trigger] indices.deep_view()[k])[1] < n_out
            by {
                if k < i as int {
                    assert(indices.deep_view()[k] =~= old_indices_dv[k]);
                } else {
                    assert(indices.deep_view()[k][1] == cols[i as int]);
                }
            }
        }

        i += 1;
    }

    (m_out, n_out, indices)
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1252);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |m: i32, n: i32, indices: &Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{},{},{:?}", m, n, indices);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::odd_cells(m, n, indices.clone());
        writeln!(out, "{}", json!({
            "input": {"m": m, "n": n, "indices": indices},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(i32, i32, Vec<Vec<i32>>)> = vec![
        (2, 3, vec![vec![0, 1], vec![1, 1]]),
        (2, 2, vec![vec![1, 1], vec![0, 0]]),
    ];
    for (m, n, indices) in &examples {
        emit(*m, *n, indices, &mut seen, &mut out, &mut count);
    }

    // Boundary and special cases with mutations
    let special_configs: Vec<(i32, i32, usize)> = vec![
        (1, 1, 1),
        (50, 50, 1),
        (1, 1, 100),
        (50, 50, 100),
        (1, 50, 50),
        (50, 1, 50),
        (10, 10, 10),
        (5, 5, 5),
        (25, 25, 50),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for &(m, n, num_idx) in &special_configs {
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let mut rows = Vec::new();
            let mut cols = Vec::new();
            for _ in 0..num_idx {
                rows.push(rng.gen_range_i64(0, (m - 1) as i64) as i32);
                cols.push(rng.gen_range_i64(0, (n - 1) as i64) as i32);
            }
            let (m_out, n_out, indices) = generate_test_case(m, n, &rows, &cols, mk);
            emit(m_out, n_out, &indices, &mut seen, &mut out, &mut count);
        }
    }

    // Random cases with diverse sizes
    let mut attempts = 0usize;
    while count < count_target && attempts < count_target * 50 {
        attempts += 1;
        let m = match attempts % 6 {
            0 => rng.gen_range_i64(1, 3) as i32,
            1 => rng.gen_range_i64(3, 10) as i32,
            2 => rng.gen_range_i64(10, 20) as i32,
            3 => rng.gen_range_i64(20, 35) as i32,
            4 => rng.gen_range_i64(35, 50) as i32,
            _ => 50,
        };
        let n = match attempts % 5 {
            0 => rng.gen_range_i64(1, 3) as i32,
            1 => rng.gen_range_i64(3, 10) as i32,
            2 => rng.gen_range_i64(10, 25) as i32,
            3 => rng.gen_range_i64(25, 45) as i32,
            _ => rng.gen_range_i64(45, 50) as i32,
        };
        let num_idx = match attempts % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 30),
            3 => rng.gen_range_usize(30, 70),
            _ => rng.gen_range_usize(70, 100),
        };
        let mut rows = Vec::new();
        let mut cols = Vec::new();
        for _ in 0..num_idx {
            rows.push(rng.gen_range_i64(0, (m - 1) as i64) as i32);
            cols.push(rng.gen_range_i64(0, (n - 1) as i64) as i32);
        }
        let mk = (rng.next_u64() % 6) as u8;
        let (m_out, n_out, indices) = generate_test_case(m, n, &rows, &cols, mk);
        emit(m_out, n_out, &indices, &mut seen, &mut out, &mut count);
    }
}
