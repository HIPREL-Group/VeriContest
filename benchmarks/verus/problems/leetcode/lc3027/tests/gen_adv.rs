use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> -1000000000 <= #[trigger] result[i][0] <= 1000000000 && -1000000000 <= result[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> -1000000000 <= #[trigger] result[j][0] <= 1000000000 && -1000000000 <= result[j][1] <= 1000000000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { -1000000000 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { -1000000000 };
        let x = if x < -1000000000 { -1000000000 } else if x > 1000000000 { 1000000000 } else { x };
        let y = if y < -1000000000 { -1000000000 } else if y > 1000000000 { 1000000000 } else { y };
        let mut accept = true;
        if result.len() > 0 {
            let last = result.len() - 1;
            assert(result[last as int].len() == 2);
            accept = result[last][0] < x || (result[last][0] == x && result[last][1] < y);
        }
        if accept {
            assert forall|j: int| 0 <= j < result.len() implies
                (result[j][0] < x || (result[j][0] == x && result[j][1] < y)) by {
                if j < result.len() - 1 { assert((result[j][0] < result[result.len() - 1][0] || (result[j][0] == result[result.len() - 1][0] && result[j][1] < result[result.len() - 1][1]))); }
            }
            let mut p = Vec::new();
            p.push(x);
            p.push(y);
            result.push(p);
        }
        i += 1;
    }
    if result.len() < 2 {
        let mut fallback: Vec<Vec<i32>> = Vec::new();
        let mut p = Vec::new();
        p.push(-1000000000);
        p.push(-1000000000);
        fallback.push(p);
        let mut p = Vec::new();
        p.push(-1000000000);
        p.push(-999999999);
        fallback.push(p);
        assert(fallback[0][1] != fallback[1][1]);
        assert(fallback[0]@ != fallback[1]@);
        fallback
    } else {
        assert forall|j: int, k: int| 0 <= j < k < result.len()
            implies result[j]@ != result[k]@ by {
            assert((result[j][0] < result[k][0] || (result[j][0] == result[k][0] && result[j][1] < result[k][1])));
        }
        result
    }
}


pub fn generate_candidate(
    n: usize,
    xs: &Vec<i32>,
    ys: &Vec<i32>,
) -> (points: Vec<Vec<i32>>)
    requires
        2 <= n <= 1000,
        xs.len() == n,
        ys.len() == n,
        forall|i: int| 0 <= i < n as int ==> -1_000_000_000 <= #[trigger] xs[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < n as int ==> -1_000_000_000 <= #[trigger] ys[i] <= 1_000_000_000,
    ensures
        2 <= points.len() <= 1000,
        forall|i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
        forall|i: int| 0 <= i < points.len()
            ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
{
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == xs.len(),
            n == ys.len(),
            2 <= n <= 1000,
            0 <= i <= n,
            points.len() == i,
            forall|k: int| 0 <= k < n as int ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < n as int ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] points[k].len() == 2,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] points[k])[0] == xs[k] && points[k][1] == ys[k],
        decreases n - i,
    {
        let mut p: Vec<i32> = Vec::new();
        p.push(xs[i]);
        p.push(ys[i]);
        assert(p.len() == 2);
        assert(p[0] == xs[i as int]);
        assert(p[1] == ys[i as int]);
        points.push(p);
        i = i + 1;
    }

    proof {
        assert forall|k: int| 0 <= k < points.len() implies
            -1_000_000_000 <= (#[trigger] points[k])[0] <= 1_000_000_000
            && -1_000_000_000 <= points[k][1] <= 1_000_000_000
        by {
            assert(points[k][0] == xs[k]);
            assert(points[k][1] == ys[k]);
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn dedupe(pts: Vec<(i32, i32)>) -> Vec<(i32, i32)> {
    let mut out: Vec<(i32, i32)> = Vec::new();
    for p in pts {
        let mut found = false;
        for q in &out {
            if q.0 == p.0 && q.1 == p.1 {
                found = true;
                break;
            }
        }
        if !found {
            out.push(p);
        }
    }
    out
}

fn ensure_distinct(rng: &mut Rng, mut pts: Vec<(i32, i32)>, lo: i32, hi: i32) -> Vec<(i32, i32)> {
    pts = dedupe(pts);
    while pts.len() < 2 {
        let x = rng.gen_range_i32(lo, hi);
        let y = rng.gen_range_i32(lo, hi);
        let mut found = false;
        for q in &pts {
            if q.0 == x && q.1 == y {
                found = true;
                break;
            }
        }
        if !found {
            pts.push((x, y));
        }
    }
    pts
}

fn gen_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<(i32, i32)> {
    let mut pts: Vec<(i32, i32)> = Vec::new();
    match mode {
        0 => {
            // random small coords
            for _ in 0..n {
                let x = rng.gen_range_i32(-10, 10);
                let y = rng.gen_range_i32(-10, 10);
                pts.push((x, y));
            }
        }
        1 => {
            // random large coords
            for _ in 0..n {
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                let y = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                pts.push((x, y));
            }
        }
        2 => {
            // collinear diagonal y = x
            for i in 0..n {
                pts.push((i as i32, i as i32));
            }
        }
        3 => {
            // anti-diagonal y = -x
            for i in 0..n {
                pts.push((i as i32, -(i as i32)));
            }
        }
        4 => {
            // same x coordinate
            let x = rng.gen_range_i32(-1000, 1000);
            for i in 0..n {
                pts.push((x, i as i32));
            }
        }
        5 => {
            // same y coordinate
            let y = rng.gen_range_i32(-1000, 1000);
            for i in 0..n {
                pts.push((i as i32, y));
            }
        }
        6 => {
            // grid pattern
            let side = (n as f64).sqrt() as usize + 1;
            for i in 0..side {
                for j in 0..side {
                    if pts.len() < n {
                        pts.push((i as i32, j as i32));
                    }
                }
            }
        }
        7 => {
            // extreme corners
            let corners = [
                (-1_000_000_000i32, -1_000_000_000i32),
                (-1_000_000_000i32, 1_000_000_000i32),
                (1_000_000_000i32, -1_000_000_000i32),
                (1_000_000_000i32, 1_000_000_000i32),
                (0, 0),
            ];
            for i in 0..n {
                let c = corners[i % corners.len()];
                pts.push((c.0 + (i / corners.len()) as i32, c.1));
            }
        }
        8 => {
            // two clusters
            for i in 0..n {
                if i % 2 == 0 {
                    pts.push((rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 100)));
                } else {
                    pts.push((rng.gen_range_i32(500, 600), rng.gen_range_i32(500, 600)));
                }
            }
        }
        9 => {
            // strictly increasing x, decreasing y (staircase)
            for i in 0..n {
                pts.push((i as i32, (n - i) as i32));
            }
        }
        _ => {
            // small coords, may have duplicates filtered
            for _ in 0..n {
                let x = rng.gen_range_i32(-5, 5);
                let y = rng.gen_range_i32(-5, 5);
                pts.push((x, y));
            }
        }
    }
    pts
}

fn print_json(points: &Vec<Vec<i32>>) {
        let mut points = points.clone();
        points.sort();
        let points = generate_test_case(points);
    print!("{{\"points\":[");
    for i in 0..points.len() {
        if i > 0 {
            print!(",");
        }
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let target_n = match mode {
            0 => 2 + (t % 8),
            1 => 3 + (t % 20),
            2 => 2 + (t % 30),
            3 => 2 + (t % 30),
            4 => 2 + (t % 50),
            5 => 2 + (t % 50),
            6 => 4 + (t % 100),
            7 => 2 + (t % 5),
            8 => 2 + (t % 40),
            9 => 2 + (t % 100),
            _ => 2 + (t % 20),
        };
        let target_n = if target_n > 1000 { 1000 } else { target_n };

        let raw = gen_mode(&mut rng, mode, target_n);
        let pts = ensure_distinct(&mut rng, raw, -1_000_000_000, 1_000_000_000);
        let n = if pts.len() > 1000 { 1000 } else { pts.len() };
        let n = if n < 2 { 2 } else { n };

        let mut xs: Vec<i32> = Vec::new();
        let mut ys: Vec<i32> = Vec::new();
        for i in 0..n {
            let (x, y) = pts[i];
            let x = x.max(-1_000_000_000).min(1_000_000_000);
            let y = y.max(-1_000_000_000).min(1_000_000_000);
            xs.push(x);
            ys.push(y);
        }

        let points = generate_candidate(n, &xs, &ys);
        print_json(&points);
    }
}
