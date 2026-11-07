use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= m <= 10_000,
        1 <= n <= 10_000,
        m * n <= 10_000,
        values.len() == m * n,
        forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= mat.len() <= 10_000,
        mat.len() == m,
        1 <= mat[0].len() <= 10_000,
        mat[0].len() == n,
        forall|r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
        forall|r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[0].len()
            ==> -100_000 <= #[trigger] mat[r][c] <= 100_000,
        mat.len() * mat[0].len() <= 10_000,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;

    while r < m
        invariant
            1 <= m <= 10_000,
            1 <= n <= 10_000,
            m * n <= 10_000,
            values.len() == m * n,
            0 <= r <= m,
            mat.len() == r,
            forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
            forall|rr: int| 0 <= rr < r as int ==> #[trigger] mat[rr].len() == n as int,
            forall|rr: int, cc: int| 0 <= rr < r as int && 0 <= cc < n as int
                ==> -100_000 <= #[trigger] mat[rr][cc] <= 100_000,
        decreases m - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;

        // Establish upper bound on r*n + c won't overflow.
        // Since r < m and m*n <= 10_000, r*n < m*n <= 10_000.
        assert(r < m);
        assert((r + 1) * n == r * n + n) by (nonlinear_arith);
        assert((r + 1) * n <= m * n) by (nonlinear_arith) requires r + 1 <= m, n >= 0;
        assert(r * n + n <= m * n);
        assert(r * n <= m * n);

        while c < n
            invariant
                1 <= m <= 10_000,
                1 <= n <= 10_000,
                m * n <= 10_000,
                values.len() == m * n,
                0 <= r < m,
                0 <= c <= n,
                row.len() == c,
                r * n + n <= m * n,
                r * n <= m * n,
                forall|i: int| 0 <= i < values.len() ==> -100_000 <= #[trigger] values[i] <= 100_000,
                forall|cc: int| 0 <= cc < c as int ==> -100_000 <= #[trigger] row[cc] <= 100_000,
            decreases n - c,
        {
            assert(r * n + c < r * n + n);
            assert(r * n + c < m * n);
            assert(r * n + c <= 10_000);
            let idx: usize = r * n + c;
            assert(idx < values.len());
            let v = values[idx];
            row.push(v);
            c = c + 1;
        }

        assert(row.len() == n);
        mat.push(row);
        r = r + 1;
    }

    assert(mat.len() == m);
    proof {
        assert(mat[0].len() == n);
        assert forall|rr: int| 0 <= rr < mat.len() implies #[trigger] mat[rr].len() == mat[0].len() by {
            assert(mat[rr].len() == n as int);
        }
    }

    mat
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

// Pick (m, n) given mode and a "size budget" constraint m*n <= 10000.
fn pick_dims(rng: &mut Rng, mode: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, rng.gen_range_usize(1, 10_000)),
        2 => (rng.gen_range_usize(1, 10_000), 1),
        3 => (2, 2),
        4 => (3, 3),
        5 => (100, 100),
        6 => (1, 10_000),
        7 => (10_000, 1),
        8 => {
            // square-ish
            let s = rng.gen_range_usize(1, 100);
            (s, s)
        }
        9 => {
            let m = rng.gen_range_usize(1, 100);
            let max_n = 10_000 / m;
            let n = rng.gen_range_usize(1, max_n.max(1));
            (m, n)
        }
        _ => {
            let m = rng.gen_range_usize(1, 50);
            let max_n = 10_000 / m;
            let n = rng.gen_range_usize(1, max_n.max(1));
            (m, n)
        }
    }
}

fn make_values(rng: &mut Rng, count: usize, mode: usize) -> Vec<i32> {
    let mut vals = Vec::with_capacity(count);
    for i in 0..count {
        let v = match mode % 5 {
            0 => rng.gen_range_i32(-100_000, 100_000),
            1 => (i as i32) % 100_001, // 0..=100000
            2 => if i % 2 == 0 { 100_000 } else { -100_000 },
            3 => 0,
            _ => {
                let pick = rng.gen_range_i32(0, 3);
                match pick {
                    0 => -100_000,
                    1 => 100_000,
                    2 => 0,
                    _ => rng.gen_range_i32(-100_000, 100_000),
                }
            }
        };
        vals.push(v);
    }
    vals
}

fn print_json(mat: &Vec<Vec<i32>>) {
    print!("{{\"mat\":[");
    for r in 0..mat.len() {
        if r > 0 {
            print!(",");
        }
        print!("[");
        for c in 0..mat[r].len() {
            if c > 0 {
                print!(",");
            }
            print!("{}", mat[r][c]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = (t + (seed as usize)) % modes;
        let (m, n) = pick_dims(&mut rng, mode);
        // Guarantee m*n <= 10000 (pick_dims ensures this, but double check).
        if m == 0 || n == 0 || m * n > 10_000 {
            continue;
        }
        let count = m * n;
        let values = make_values(&mut rng, count, mode);
        let mat = generate_test_case(m, n, &values);
        print_json(&mat);
    }
}