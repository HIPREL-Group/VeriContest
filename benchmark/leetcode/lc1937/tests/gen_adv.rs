use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    fill_val: i32,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= m <= 100_000,
        1 <= n <= 100_000,
        m * n <= 100_000,
        0 <= fill_val <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        1 <= result[0].len() <= 100_000,
        result.len() * result[0].len() <= 100_000,
        forall|r: int|
            0 <= r < result.len() ==> (#[trigger] result[r]).len() == result[0].len(),
        forall|r: int, c: int|
            0 <= r < result.len() && 0 <= c < result[0].len()
                ==> 0 <= #[trigger] result[r][c] <= 100_000,
{
    // Build a single row
    let mut row: Vec<i32> = Vec::new();
    let mut c: usize = 0;
    while c < n
        invariant
            0 <= c <= n,
            row.len() == c,
            0 <= fill_val <= 100_000,
            forall|k: int| 0 <= k < c as int ==> #[trigger] row[k] == fill_val,
        decreases n - c,
    {
        row.push(fill_val);
        c = c + 1;
    }

    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < m
        invariant
            0 <= r <= m,
            result.len() == r,
            row.len() == n,
            0 <= fill_val <= 100_000,
            forall|k: int| 0 <= k < n as int ==> #[trigger] row[k] == fill_val,
            forall|rr: int| 0 <= rr < r as int ==> (#[trigger] result[rr]).len() == n as nat,
            forall|rr: int, cc: int|
                0 <= rr < r as int && 0 <= cc < n as int
                    ==> #[trigger] (result[rr])[cc] == fill_val,
        decreases m - r,
    {
        // Clone row
        let mut row_copy: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                row_copy.len() == i,
                row.len() == n,
                0 <= fill_val <= 100_000,
                forall|k: int| 0 <= k < n as int ==> #[trigger] row[k] == fill_val,
                forall|k: int| 0 <= k < i as int ==> #[trigger] row_copy[k] == fill_val,
            decreases n - i,
        {
            row_copy.push(row[i]);
            i = i + 1;
        }
        result.push(row_copy);
        r = r + 1;
    }

    proof {
        assert(result.len() == m);
        assert(result[0].len() == n);
        assert forall|rr: int, cc: int|
            0 <= rr < result.len() && 0 <= cc < result[0].len()
                implies 0 <= #[trigger] result[rr][cc] <= 100_000 by {
            assert(result[rr][cc] == fill_val);
        }
    }

    result
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_dims(rng: &mut Rng, mode: usize) -> (usize, usize) {
    match mode {
        0 => (1, 1),
        1 => (1, rng.gen_range_usize(1, 100_000)),
        2 => (rng.gen_range_usize(1, 100_000), 1),
        3 => (100_000, 1),
        4 => (1, 100_000),
        5 => {
            // roughly square-ish
            let m = rng.gen_range_usize(1, 316);
            let max_n = 100_000 / m;
            let n = if max_n == 0 { 1 } else { rng.gen_range_usize(1, max_n) };
            (m, n)
        }
        6 => (2, rng.gen_range_usize(1, 50_000)),
        7 => (rng.gen_range_usize(1, 50_000), 2),
        8 => {
            let m = rng.gen_range_usize(1, 100);
            let n = rng.gen_range_usize(1, 100);
            (m, n)
        }
        9 => (316, 316),
        _ => {
            let m = rng.gen_range_usize(1, 1000);
            let max_n = 100_000 / m;
            let n = if max_n == 0 { 1 } else { rng.gen_range_usize(1, max_n) };
            (m, n)
        }
    }
}

fn pick_fill(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 100_000,
        2 => 1,
        3 => rng.gen_range_i32(0, 100_000),
        _ => rng.gen_range_i32(0, 100_000),
    }
}

fn print_json(points: &Vec<Vec<i32>>) {
    print!("{{\"points\":[");
    for r in 0..points.len() {
        if r > 0 {
            print!(",");
        }
        print!("[");
        for c in 0..points[r].len() {
            if c > 0 {
                print!(",");
            }
            print!("{}", points[r][c]);
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
        let mode = t % modes;
        let (m, n) = pick_dims(&mut rng, mode);
        // ensure m*n <= 100_000
        let (m, n) = if m.checked_mul(n).unwrap_or(usize::MAX) > 100_000 {
            let max_n = 100_000 / m.max(1);
            (m, if max_n == 0 { 1 } else { max_n })
        } else {
            (m, n)
        };
        let fill = pick_fill(&mut rng, mode);
        let pts = generate_test_case(m, n, fill);
        print_json(&pts);
    }
}