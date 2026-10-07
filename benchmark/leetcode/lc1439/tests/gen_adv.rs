use vstd::prelude::*;

verus! {

pub open spec fn total_combos(mat: Seq<Vec<i32>>, row: int) -> int
    decreases mat.len() - row
{
    if row >= mat.len() as int { 1 }
    else { mat[row].len() as int * total_combos(mat, row + 1) }
}

/// total_combos is always >= 1 when every row has length >= 1.
proof fn lemma_total_combos_ge1(mat: Seq<Vec<i32>>, row: int)
    requires
        0 <= row <= mat.len(),
        forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1,
    ensures
        total_combos(mat, row) >= 1,
    decreases mat.len() - row,
{
    if row < mat.len() as int {
        lemma_total_combos_ge1(mat, row + 1);
        assert(mat[row].len() >= 1);
        assert(total_combos(mat, row) == mat[row].len() as int * total_combos(mat, row + 1));
        assert(mat[row].len() as int >= 1);
        assert(total_combos(mat, row + 1) >= 1);
        assert(mat[row].len() as int * total_combos(mat, row + 1) >= 1) by(nonlinear_arith)
            requires mat[row].len() as int >= 1, total_combos(mat, row + 1) >= 1;
    }
}

/// Multiplying a <= b by c >= 1 preserves <=
proof fn lemma_mul_le(a: int, b: int, c: int)
    requires
        0 <= a <= b,
        c >= 1,
    ensures
        a * c <= b * c,
{
    assert(b - a >= 0);
    assert(c >= 1);
    // (b - a) * c >= 0
    // b*c - a*c >= 0
    // a*c <= b*c
    assert((b - a) * c == b * c - a * c) by(nonlinear_arith);
    assert((b - a) * c >= 0) by(nonlinear_arith)
        requires b - a >= 0, c >= 1;
}

pub fn generate_test_case(
    // Construction parameters:
    // - m: number of rows (1..=40)
    // - n: number of columns (1..=40)
    // - base_vals: flat array of m*n base values in [1, 5000], will be sorted per row
    // - deltas: flat array of m*(n-1) non-negative deltas for building sorted rows
    // - k_raw: raw k value (will be clamped)
    // - mutation_kind: selects mutation strategy
    m: u32,
    n: u32,
    base_vals: &Vec<i32>,
    deltas: &Vec<i32>,
    k_raw: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 40,
        1 <= n <= 40,
        base_vals.len() == m as int,
        deltas.len() == m as int * (n as int - 1),
        forall|i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 5000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i] <= 100,
        // Ensure sorted row values stay <= 5000:
        // base + sum of deltas per row <= 5000
        // With n<=40 columns and delta<=100, max sum of deltas = 39*100 = 3900
        // base <= 5000 and base + 3900 <= 5000 is NOT always true,
        // so we require base_vals[i] + (n-1)*100 <= 5000
        forall|i: int| 0 <= i < base_vals.len() ==>
            #[trigger] base_vals[i] as int + (n as int - 1) * 100 <= 5000,
        1 <= k_raw <= 200,
    ensures
        1 <= result.0.len() <= 40,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() >= 1 && result.0[i].len() <= 40,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i]).len() == result.0[0].len(),
        forall|i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() ==>
            1 <= #[trigger] result.0[i][j] <= 5000,
        forall|i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() - 1 ==>
            #[trigger] result.0[i][j] <= result.0[i][j + 1],
        1 <= result.1 <= 200,
        result.1 as int <= total_combos(result.0@, 0),
{
    // Build the matrix row by row
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut row_idx: u32 = 0;

    while row_idx < m
        invariant
            0 <= row_idx <= m,
            1 <= m <= 40,
            1 <= n <= 40,
            mat.len() == row_idx as int,
            base_vals.len() == m as int,
            deltas.len() == m as int * (n as int - 1),
            forall|i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 5000,
            forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i] <= 100,
            forall|i: int| 0 <= i < base_vals.len() ==>
                #[trigger] base_vals[i] as int + (n as int - 1) * 100 <= 5000,
            // All built rows have length n
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == n as int,
            // All elements in [1, 5000]
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() ==>
                1 <= #[trigger] mat[i][j] <= 5000,
            // Each row is sorted
            forall|i: int, j: int| 0 <= i < mat.len() && 0 <= j < mat[i].len() - 1 ==>
                #[trigger] mat[i][j] <= mat[i][j + 1],
        decreases m - row_idx,
    {
        proof {
            assert(row_idx < m);
            assert((row_idx as int) < base_vals@.len());
        }
        let base = base_vals[row_idx as usize];
        let mut row: Vec<i32> = Vec::new();
        row.push(base);

        let mut col_idx: u32 = 0;

        while col_idx < n - 1
            invariant
                0 <= col_idx <= n - 1,
                1 <= n <= 40,
                1 <= m <= 40,
                row.len() == col_idx as int + 1,
                0 <= row_idx < m,
                deltas.len() == m as int * (n as int - 1),
                forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i] <= 100,
                1 <= base <= 5000,
                base as int + (n as int - 1) * 100 <= 5000,
                // All elements so far are in [1, 5000]
                forall|j: int| 0 <= j < row.len() ==> 1 <= #[trigger] row[j] <= 5000,
                // Row so far is sorted
                forall|j: int| 0 <= j < row.len() - 1 ==> #[trigger] row[j] <= row[j + 1],
                // Last element is bounded
                row[row.len() - 1] as int <= base as int + (col_idx as int) * 100,
            decreases n - 1 - col_idx,
        {
            proof {
                // row_idx < 40, n-1 < 40, col_idx < 40
                // so row_idx*(n-1) < 40*40 = 1600, + col_idx < 1640
                assert((row_idx as int) * (n as int - 1) < 1600) by(nonlinear_arith)
                    requires 0 <= row_idx < 40, 0 <= n - 1 < 40;
            }
            let d_idx: usize = (row_idx as usize) * ((n - 1) as usize) + (col_idx as usize);
            proof {
                // row_idx < m, col_idx < n-1
                // d_idx = row_idx*(n-1) + col_idx < m*(n-1) = deltas.len()
                assert((row_idx as int) * (n as int - 1) >= 0) by(nonlinear_arith)
                    requires row_idx >= 0, n >= 1;
                assert(d_idx as int == (row_idx as int) * (n as int - 1) + (col_idx as int));
                assert((row_idx as int) * (n as int - 1) + (col_idx as int) < (m as int) * (n as int - 1)) by(nonlinear_arith)
                    requires 0 <= row_idx < m, 0 <= col_idx < n - 1, n >= 1;
                assert(d_idx < deltas.len());
            }
            let prev = row[col_idx as usize];
            let next = (prev + deltas[d_idx]) as i32;

            proof {
                // next <= base + (col_idx+1)*100 <= base + (n-1)*100 <= 5000
                assert(prev as int <= base as int + col_idx as int * 100);
                assert(deltas[d_idx as int] <= 100);
                assert(next as int <= base as int + (col_idx as int + 1) * 100);
                assert(next as int <= base as int + (n as int - 1) * 100);
                assert(next as int <= 5000);
                assert(next >= prev);
                // next >= 1 since prev >= 1 and delta >= 0
                assert(next >= 1);
            }

            row.push(next);

            proof {
                assert forall|j: int| 0 <= j < row.len() - 1 implies #[trigger] row[j] <= row[j + 1] by {
                    if j == row.len() - 2 {
                        assert(row[j] == prev);
                        assert(row[j + 1] == next);
                    }
                };
            }

            col_idx += 1;
        }

        proof {
            assert(row.len() == n as int);
        }

        mat.push(row);

        proof {
            assert(mat[mat.len() - 1].len() == n as int);
            assert forall|i: int| 0 <= i < mat.len() implies (#[trigger] mat[i]).len() == n as int by {};
        }

        row_idx += 1;
    }

    // mat is now m x n, sorted rows, values in [1, 5000]
    // Clamp k to be <= total_combos
    // total_combos = n^m which is >= 1 (since n >= 1, m >= 1)
    proof {
        lemma_total_combos_ge1(mat@, 0);
    }

    // Compute total_combos at runtime, tracking that combos <= total_combos(mat@, ci)
    // We cap at 201 to avoid overflow (we only need to know if >= k_raw)
    let mut combos: i64 = 1;
    let mut ci: u32 = m;
    // Start from the back: total_combos(mat@, m) == 1
    // Then multiply by mat[m-1].len(), mat[m-2].len(), etc.
    while ci > 0
        invariant
            0 <= ci <= m,
            mat.len() == m as int,
            1 <= n <= 40,
            1 <= combos <= 201,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == n as int,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() >= 1,
            combos as int <= total_combos(mat@, ci as int),
        decreases ci,
    {
        ci = ci - 1;
        let row_len = mat[ci as usize].len() as i64;
        proof {
            let tc_next = total_combos(mat@, ci as int + 1);
            let rl = row_len as int;
            assert(total_combos(mat@, ci as int) == rl * tc_next);
            assert(combos as int <= tc_next);
            assert(1 <= rl <= 40);
            lemma_total_combos_ge1(mat@, ci as int + 1);
            assert(tc_next >= 1);
            lemma_mul_le(combos as int, tc_next, rl);
            // combos * rl <= tc_next * rl, and tc_next * rl == rl * tc_next == total_combos(ci)
            assert(tc_next * rl == rl * tc_next) by(nonlinear_arith);
        }
        // combos in [1, 201], row_len in [1, 40], product <= 8040 fits i64
        assert(combos >= 1 && combos <= 201);
        assert(row_len >= 1 && row_len <= 40);
        assert(combos * row_len <= 201 * 40) by(nonlinear_arith)
            requires combos >= 1, combos <= 201, row_len >= 1, row_len <= 40;
        let new_combos: i64 = combos * row_len;
        assert(new_combos == combos * row_len);
        assert(combos >= 1 && row_len >= 1);
        assert(combos * row_len >= 1) by(nonlinear_arith)
            requires combos >= 1, row_len >= 1;

        if new_combos > 200 {
            combos = 201;
            assert(1 <= combos <= 201);
            assert(combos as int <= total_combos(mat@, ci as int));
        } else {
            combos = new_combos;
            assert(1 <= combos <= 201);
            assert(combos as int <= total_combos(mat@, ci as int));
        }
    }
    // Now combos <= total_combos(mat@, 0) and combos is in [1, 201]

    // k is in [1, min(k_raw, combos, 200)]
    let capped_combos: i32 = if combos > 200 { 200 } else { combos as i32 };
    let k: i32 = if k_raw <= capped_combos { k_raw } else { capped_combos };

    // Apply mutations
    let final_k: i32 = if mutation_kind == 0 {
        k
    } else if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        capped_combos
    } else if mutation_kind == 3 && k > 1 {
        (k - 1) as i32
    } else if mutation_kind == 4 && k < capped_combos && k < 200 {
        (k + 1) as i32
    } else {
        k
    };

    proof {
        // final_k <= capped_combos <= combos <= total_combos(mat@, 0)
        // final_k >= 1 (all branches produce >= 1)
        // final_k <= 200 (capped_combos <= 200)
    }

    (mat, final_k)
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

fn print_json(mat: &Vec<Vec<i32>>, k: i32) {
    print!("{{\"mat\":[");
    for i in 0..mat.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..mat[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", mat[i][j]);
        }
        print!("]");
    }
    println!("],\"k\":{}}}", k);
}

fn total_combos_rt(mat: &[Vec<i32>]) -> i64 {
    let mut c: i64 = 1;
    for row in mat {
        c = c.saturating_mul(row.len() as i64);
        if c > 200 {
            return 201;
        }
    }
    c
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1439);
    let mut rng = Rng::new(seed);

    let mut emit = |mat: Vec<Vec<i32>>, k: i32| {
        print_json(&mat, k);
    };

    emit(vec![vec![1, 3, 11], vec![2, 4, 6]], 5);
    emit(vec![vec![1, 3, 11], vec![2, 4, 6]], 9);
    emit(vec![vec![1, 10, 10], vec![1, 4, 5], vec![2, 3, 6]], 7);

    for mk in 0u8..=4 {
        let (mat, k) = generate_test_case(1 as u32, 1 as u32, &vec![1], &vec![], 1, mk);
        emit(mat, k);
    }
    {
        let (mat, k) = generate_test_case(1 as u32, 1 as u32, &vec![5000], &vec![], 1, 0);
        emit(mat, k);
    }
    for mk in 0u8..=4 {
        let (mat, k) = generate_test_case(1 as u32, 5 as u32, &vec![1], &vec![1, 1, 1, 1], 3, mk);
        emit(mat, k);
    }
    for mk in 0u8..=4 {
        let (mat, k) = generate_test_case(3 as u32, 1 as u32, &vec![1, 2, 3], &vec![], 1, mk);
        emit(mat, k);
    }
    for mk in 0u8..=4 {
        let base_vals = vec![1, 2];
        let deltas = vec![2, 10, 2, 2];
        let (mat, k) = generate_test_case(2 as u32, 3 as u32, &base_vals, &deltas, 5, mk);
        emit(mat, k);
    }
    for mk in 0u8..=4 {
        let base_vals = vec![1, 1, 2];
        let deltas = vec![9, 0, 3, 1, 1, 3];
        let (mat, k) = generate_test_case(3 as u32, 3 as u32, &base_vals, &deltas, 7, mk);
        emit(mat, k);
    }

    for _ in 0..10 {
        let m = rng.gen_range_usize(1, 5);
        let n = rng.gen_range_usize(1, 5);
        let max_base = std::cmp::min(5000, 5000 - (n as i64 - 1) * 100) as i32;
        let max_base = std::cmp::max(1, max_base);
        let base_vals: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, max_base as i64) as i32).collect();
        let deltas: Vec<i32> = (0..m * (n - 1)).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
        let tc = total_combos_rt(&{
            let mut mat = Vec::new();
            for i in 0..m {
                let mut row = vec![base_vals[i]];
                for j in 0..(n - 1) {
                    row.push(row.last().unwrap() + deltas[i * (n - 1) + j]);
                }
                mat.push(row);
            }
            mat
        });
        let max_k = std::cmp::min(200, tc as i32);
        let k = rng.gen_range_i64(1, max_k as i64) as i32;
        let mk = rng.gen_range_i64(0, 4) as u8;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
    }

    for _ in 0..15 {
        let m = rng.gen_range_usize(2, 6);
        let n = rng.gen_range_usize(2, 6);
        let max_base = std::cmp::max(1, std::cmp::min(5000, 5000 - (n as i64 - 1) * 100) as i32);
        let base_vals: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, max_base as i64) as i32).collect();
        let deltas: Vec<i32> = (0..m * (n - 1)).map(|_| rng.gen_range_i64(0, 50) as i32).collect();
        let tc = total_combos_rt(&{
            let mut mat = Vec::new();
            for i in 0..m {
                let mut row = vec![base_vals[i]];
                for j in 0..(n - 1) {
                    row.push(row.last().unwrap() + deltas[i * (n - 1) + j]);
                }
                mat.push(row);
            }
            mat
        });
        let max_k = std::cmp::min(200, tc as i32);
        let k = rng.gen_range_i64(1, max_k as i64) as i32;
        let mk = rng.gen_range_i64(0, 4) as u8;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
    }

    for _ in 0..5 {
        let m = rng.gen_range_usize(5, 10);
        let n = rng.gen_range_usize(1, 4);
        let max_base = std::cmp::max(1, std::cmp::min(5000, 5000 - (n as i64 - 1) * 100) as i32);
        let base_vals: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, max_base as i64) as i32).collect();
        let deltas: Vec<i32> = (0..m * (n - 1)).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
        let tc = total_combos_rt(&{
            let mut mat = Vec::new();
            for i in 0..m {
                let mut row = vec![base_vals[i]];
                for j in 0..(n - 1) {
                    row.push(row.last().unwrap() + deltas[i * (n - 1) + j]);
                }
                mat.push(row);
            }
            mat
        });
        let max_k = std::cmp::min(200, tc as i32);
        let k = rng.gen_range_i64(1, max_k as i64) as i32;
        let mk = rng.gen_range_i64(0, 4) as u8;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
    }

    for _ in 0..3 {
        let m = 8;
        let n = rng.gen_range_usize(2, 4);
        let max_base = std::cmp::max(1, std::cmp::min(5000, 5000 - (n as i64 - 1) * 100) as i32);
        let base_vals: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, max_base as i64) as i32).collect();
        let deltas: Vec<i32> = (0..m * (n - 1)).map(|_| rng.gen_range_i64(0, 10) as i32).collect();
        let k = rng.gen_range_i64(1, 200) as i32;
        let mk = rng.gen_range_i64(0, 4) as u8;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
    }

    {
        let m = 5;
        let n = 5;
        let base_vals = vec![1; m];
        let deltas = vec![0; m * (n - 1)];
        let (mat, k) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, 200, 0);
        emit(mat, k);
    }
    {
        let m = 3;
        let n = 1;
        let base_vals = vec![5000; m];
        let deltas: Vec<i32> = vec![];
        let (mat, k) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, 1, 0);
        emit(mat, k);
    }
    for mk in 0u8..=4 {
        let m = 4;
        let n = 4;
        let base_vals = vec![1; m];
        let deltas = vec![1; m * (n - 1)];
        let k = rng.gen_range_i64(1, 200) as i32;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
    }

    for t in 0..200 {
        let m = rng.gen_range_usize(1, 8);
        let n = rng.gen_range_usize(1, 6);
        let max_base = std::cmp::max(1, std::cmp::min(5000, 5000 - (n as i64 - 1) * 100) as i32);
        let base_vals: Vec<i32> = (0..m).map(|_| rng.gen_range_i64(1, max_base as i64) as i32).collect();
        let deltas: Vec<i32> = (0..m * (n - 1)).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
        let tc = total_combos_rt(&{
            let mut mat = Vec::new();
            for i in 0..m {
                let mut row = vec![base_vals[i]];
                for j in 0..(n - 1) {
                    row.push(row.last().unwrap() + deltas[i * (n - 1) + j]);
                }
                mat.push(row);
            }
            mat
        });
        let max_k = std::cmp::min(200, std::cmp::max(1, tc as i32));
        let k = rng.gen_range_i64(1, max_k as i64) as i32;
        let mk = rng.gen_range_i64(0, 4) as u8;
        let (mat, k_out) = generate_test_case(m as u32, n as u32, &base_vals, &deltas, k, mk);
        emit(mat, k_out);
        let _ = t;
    }
}
