use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    xs: &Vec<i32>,
    ys: &Vec<i32>,
) -> (points: Vec<Vec<i32>>)
    requires
        2 <= n <= 50,
        xs.len() == n,
        ys.len() == n,
        forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] xs[i] <= 50,
        forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] ys[i] <= 50,
        forall|i: int, j: int| 0 <= i < j < n as int ==>
            (#[trigger] xs[i] != #[trigger] xs[j]) || (#[trigger] ys[i] != #[trigger] ys[j]),
    ensures
        2 <= points.len() <= 50,
        forall|i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
        forall|i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 50,
        forall|i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][1] <= 50,
        forall|i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
{
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            points.len() == k,
            xs.len() == n,
            ys.len() == n,
            forall|i: int| 0 <= i < k as int ==> #[trigger] points[i].len() == 2,
            forall|i: int| 0 <= i < k as int ==> #[trigger] points[i][0] == xs[i],
            forall|i: int| 0 <= i < k as int ==> #[trigger] points[i][1] == ys[i],
            forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] xs[i] <= 50,
            forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] ys[i] <= 50,
        decreases n - k,
    {
        let mut p: Vec<i32> = Vec::new();
        p.push(xs[k]);
        p.push(ys[k]);
        assert(p.len() == 2);
        assert(p[0] == xs[k as int]);
        assert(p[1] == ys[k as int]);
        points.push(p);
        k = k + 1;
    }

    proof {
        assert forall|i: int, j: int| 0 <= i < j < points.len() implies #[trigger] points[i] != #[trigger] points[j]
        by {
            assert(points[i][0] == xs[i]);
            assert(points[i][1] == ys[i]);
            assert(points[j][0] == xs[j]);
            assert(points[j][1] == ys[j]);
            assert(xs[i] != xs[j] || ys[i] != ys[j]);
            if points[i] == points[j] {
                assert(points[i][0] == points[j][0]);
                assert(points[i][1] == points[j][1]);
                assert(false);
            }
        }
    }

    points
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn make_distinct(rng: &mut Rng, n: usize, xs: &mut Vec<i32>, ys: &mut Vec<i32>,
                 x_lo: i32, x_hi: i32, y_lo: i32, y_hi: i32) {
    xs.clear();
    ys.clear();
    let mut used: std::collections::HashSet<(i32, i32)> = std::collections::HashSet::new();
    let mut attempts = 0;
    while xs.len() < n && attempts < 100000 {
        let x = rng.gen_range_i32(x_lo, x_hi);
        let y = rng.gen_range_i32(y_lo, y_hi);
        if !used.contains(&(x, y)) {
            used.insert((x, y));
            xs.push(x);
            ys.push(y);
        }
        attempts += 1;
    }
    // Fallback: fill with grid
    let mut x = 0i32;
    let mut y = 0i32;
    while xs.len() < n {
        if !used.contains(&(x, y)) {
            used.insert((x, y));
            xs.push(x);
            ys.push(y);
        }
        x += 1;
        if x > 50 {
            x = 0;
            y += 1;
            if y > 50 {
                break;
            }
        }
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, Vec<i32>, Vec<i32>) {
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();

    match mode {
        0 => {
            // Minimal n=2
            let n = 2;
            make_distinct(rng, n, &mut xs, &mut ys, 0, 50, 0, 50);
            (n, xs, ys)
        }
        1 => {
            // Max n=50 random
            let n = 50;
            make_distinct(rng, n, &mut xs, &mut ys, 0, 50, 0, 50);
            (n, xs, ys)
        }
        2 => {
            // Diagonal line ascending
            let n = rng.gen_range_usize(2, 50);
            let mut used: std::collections::HashSet<(i32,i32)> = std::collections::HashSet::new();
            let mut i = 0i32;
            while (xs.len() as usize) < n && i <= 50 {
                if !used.contains(&(i, i)) {
                    used.insert((i, i));
                    xs.push(i);
                    ys.push(i);
                }
                i += 1;
            }
            // fill remainder with unique
            let mut x = 0i32;
            let mut y = 0i32;
            while xs.len() < n {
                if !used.contains(&(x, y)) {
                    used.insert((x, y));
                    xs.push(x);
                    ys.push(y);
                }
                x += 1;
                if x > 50 { x = 0; y += 1; if y > 50 { break; } }
            }
            let n = xs.len();
            (n, xs, ys)
        }
        3 => {
            // Anti-diagonal
            let n = rng.gen_range_usize(2, 50);
            let mut used: std::collections::HashSet<(i32,i32)> = std::collections::HashSet::new();
            let mut i = 0i32;
            while xs.len() < n && i <= 50 {
                let yv = 50 - i;
                if !used.contains(&(i, yv)) {
                    used.insert((i, yv));
                    xs.push(i);
                    ys.push(yv);
                }
                i += 1;
            }
            let mut x = 0i32;
            let mut y = 0i32;
            while xs.len() < n {
                if !used.contains(&(x, y)) {
                    used.insert((x, y));
                    xs.push(x);
                    ys.push(y);
                }
                x += 1;
                if x > 50 { x = 0; y += 1; if y > 50 { break; } }
            }
            let n = xs.len();
            (n, xs, ys)
        }
        4 => {
            // All same x, different y
            let n = rng.gen_range_usize(2, 50);
            let xv = rng.gen_range_i32(0, 50);
            for i in 0..n {
                xs.push(xv);
                ys.push(i as i32);
            }
            (n, xs, ys)
        }
        5 => {
            // All same y, different x
            let n = rng.gen_range_usize(2, 50);
            let yv = rng.gen_range_i32(0, 50);
            for i in 0..n {
                xs.push(i as i32);
                ys.push(yv);
            }
            (n, xs, ys)
        }
        6 => {
            // Small grid cluster
            let n = rng.gen_range_usize(2, 25);
            make_distinct(rng, n, &mut xs, &mut ys, 0, 4, 0, 4);
            (n, xs, ys)
        }
        7 => {
            // Corners
            let coords = [(0,0),(0,50),(50,0),(50,50),(25,25)];
            let n = rng.gen_range_usize(2, 5);
            for i in 0..n {
                xs.push(coords[i].0);
                ys.push(coords[i].1);
            }
            (n, xs, ys)
        }
        8 => {
            // Two points
            let n = 2;
            let x1 = rng.gen_range_i32(0, 50);
            let y1 = rng.gen_range_i32(0, 50);
            let mut x2 = rng.gen_range_i32(0, 50);
            let mut y2 = rng.gen_range_i32(0, 50);
            if x1 == x2 && y1 == y2 {
                if x2 < 50 { x2 += 1; } else { x2 -= 1; }
            }
            xs.push(x1); ys.push(y1);
            xs.push(x2); ys.push(y2);
            (n, xs, ys)
        }
        9 => {
            // Random medium
            let n = rng.gen_range_usize(5, 30);
            make_distinct(rng, n, &mut xs, &mut ys, 0, 50, 0, 50);
            (n, xs, ys)
        }
        _ => {
            let n = rng.gen_range_usize(2, 50);
            make_distinct(rng, n, &mut xs, &mut ys, 0, 50, 0, 50);
            (n, xs, ys)
        }
    }
}

fn validate(n: usize, xs: &Vec<i32>, ys: &Vec<i32>) -> bool {
    if n < 2 || n > 50 { return false; }
    if xs.len() != n || ys.len() != n { return false; }
    for i in 0..n {
        if xs[i] < 0 || xs[i] > 50 { return false; }
        if ys[i] < 0 || ys[i] > 50 { return false; }
    }
    for i in 0..n {
        for j in (i+1)..n {
            if xs[i] == xs[j] && ys[i] == ys[j] { return false; }
        }
    }
    true
}

fn print_json(points: &Vec<Vec<i32>>) {
    print!("{{\"points\":[");
    for i in 0..points.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", points[i][0], points[i][1]);
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
        let (n, xs, ys) = gen_mode(&mut rng, mode);
        if !validate(n, &xs, &ys) {
            // Fallback - emit a trivial 2-point test
            let xs2 = vec![0i32, 1i32];
            let ys2 = vec![0i32, 1i32];
            let points = generate_test_case(2, &xs2, &ys2);
            print_json(&points);
            continue;
        }
        let points = generate_test_case(n, &xs, &ys);
        print_json(&points);
    }
}