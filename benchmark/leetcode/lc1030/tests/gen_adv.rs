use vstd::prelude::*;

verus! {

pub open spec fn valid_input(rows: i32, cols: i32, r_center: i32, c_center: i32) -> bool {
    1 <= rows <= 100
        && 1 <= cols <= 100
        && 0 <= r_center < rows
        && 0 <= c_center < cols
}

pub fn generate_test_case(
    rows_hint: i32,
    cols_hint: i32,
    r_bias: i32,
    c_bias: i32,
    force_single_row: bool,
    force_single_col: bool,
    force_corner: u8,
) -> (tc: (i32, i32, i32, i32))
    requires
        0 <= rows_hint <= 99,
        0 <= cols_hint <= 99,
        0 <= r_bias <= 99,
        0 <= c_bias <= 99,
        force_corner <= 4,
    ensures
        valid_input(tc.0, tc.1, tc.2, tc.3),
{
    let mut rows = rows_hint + 1;
    let mut cols = cols_hint + 1;

    if force_single_row {
        rows = 1;
    }
    if force_single_col {
        cols = 1;
    }

    let mut r_center = if rows > 0 { r_bias % rows } else { 0 };
    let mut c_center = if cols > 0 { c_bias % cols } else { 0 };

    if force_corner == 1 {
        r_center = 0;
        c_center = 0;
    } else if force_corner == 2 {
        r_center = 0;
        c_center = cols - 1;
    } else if force_corner == 3 {
        r_center = rows - 1;
        c_center = 0;
    } else if force_corner == 4 {
        r_center = rows - 1;
        c_center = cols - 1;
    }

    assert(1 <= rows <= 100);
    assert(1 <= cols <= 100);
    assert(rows > 0);
    assert(cols > 0);
    assert(0 <= r_center);
    assert(r_center < rows);
    assert(0 <= c_center);
    assert(c_center < cols);

    (rows, cols, r_center, c_center)
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 0
    }
}

fn mode_case(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32, bool, bool, u8) {
    match mode {
        0 => (0, 0, 0, 0, false, false, 0), // absolute minimum 1x1
        1 => (99, 99, 50, 50, false, false, 0), // maximum dimensions
        2 => (99, 0, 77, 0, false, true, 0), // 100x1
        3 => (0, 99, 0, 66, true, false, 0), // 1x100
        4 => (99, 99, 0, 0, false, false, 1), // top-left corner
        5 => (99, 99, 0, 0, false, false, 2), // top-right corner
        6 => (99, 99, 0, 0, false, false, 3), // bottom-left corner
        7 => (99, 99, 0, 0, false, false, 4), // bottom-right corner
        8 => {
            let rows_hint = rng.gen_range_i32(1, 98);
            let cols_hint = rng.gen_range_i32(1, 98);
            let rows = rows_hint + 1;
            let cols = cols_hint + 1;
            (rows_hint, cols_hint, rows / 2, cols / 2, false, false, 0) // center-ish
        }
        9 => {
            let rows_hint = rng.gen_range_i32(0, 99);
            let cols_hint = rng.gen_range_i32(0, 99);
            (rows_hint, cols_hint, 99, 99, false, false, 0) // large bias modulo behavior
        }
        10 => {
            let cols_hint = rng.gen_range_i32(0, 99);
            (0, cols_hint, 0, rng.gen_range_i32(0, 99), true, false, 0) // single row random center
        }
        11 => {
            let rows_hint = rng.gen_range_i32(0, 99);
            (rows_hint, 0, rng.gen_range_i32(0, 99), 0, false, true, 0) // single col random center
        }
        _ => {
            let rows_hint = rng.gen_range_i32(0, 99);
            let cols_hint = rng.gen_range_i32(0, 99);
            let force_single_row = rng.gen_bool() && rng.gen_bool();
            let force_single_col = rng.gen_bool() && rng.gen_bool();
            let corner = rng.gen_range_u64(0, 4) as u8;
            (
                rows_hint,
                cols_hint,
                rng.gen_range_i32(0, 99),
                rng.gen_range_i32(0, 99),
                force_single_row,
                force_single_col,
                corner,
            )
        }
    }
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total_cases: usize = 200;
    let adversarial_modes: usize = 12;

    for i in 0..total_cases {
        let mode = if i < 120 {
            i % adversarial_modes
        } else {
            1000 + (i % 17)
        };

        let (rows_hint, cols_hint, r_bias, c_bias, force_single_row, force_single_col, force_corner) =
            mode_case(&mut rng, mode);

        let (rows, cols, r_center, c_center) = generate_test_case(
            rows_hint,
            cols_hint,
            r_bias,
            c_bias,
            force_single_row,
            force_single_col,
            force_corner,
        );

        writeln!(
            out,
            "{{\"rows\":{},\"cols\":{},\"r_center\":{},\"c_center\":{}}}",
            rows, cols, r_center, c_center
        )
        .unwrap();
    }
}