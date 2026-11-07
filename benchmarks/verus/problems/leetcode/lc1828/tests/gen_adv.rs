use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    points_raw: &Vec<(i32, i32)>,
    queries_raw: &Vec<(i32, i32, i32)>,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        1 <= points_raw.len() <= 500,
        1 <= queries_raw.len() <= 500,
        forall|i: int| 0 <= i < points_raw.len() ==>
            0 <= (#[trigger] points_raw[i]).0 <= 500 && 0 <= points_raw[i].1 <= 500,
        forall|j: int| 0 <= j < queries_raw.len() ==>
            0 <= (#[trigger] queries_raw[j]).0 <= 500 && 0 <= queries_raw[j].1 <= 500
                && 1 <= queries_raw[j].2 <= 500,
    ensures
        ({
            let points = result.0;
            let queries = result.1;
            &&& 1 <= points.len() <= 500
            &&& points.len() == points_raw.len()
            &&& forall|i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2
            &&& forall|i: int| 0 <= i < points.len() ==>
                  0 <= #[trigger] points[i][0] <= 500 && 0 <= points[i][1] <= 500
            &&& 1 <= queries.len() <= 500
            &&& queries.len() == queries_raw.len()
            &&& forall|j: int| 0 <= j < queries.len() ==> #[trigger] queries[j].len() == 3
            &&& forall|j: int| 0 <= j < queries.len() ==>
                  0 <= #[trigger] queries[j][0] <= 500 && 0 <= queries[j][1] <= 500
                    && 1 <= queries[j][2] <= 500
        }),
{
    let mut points: Vec<Vec<i32>> = Vec::new();
    let n = points_raw.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == points_raw.len(),
            i <= n,
            points.len() == i,
            forall|k: int| 0 <= k < points.len() ==> #[trigger] points[k].len() == 2,
            forall|k: int| 0 <= k < points.len() ==>
                #[trigger] points[k][0] == points_raw[k].0 && points[k][1] == points_raw[k].1,
            forall|k: int| 0 <= k < points_raw.len() ==>
                0 <= (#[trigger] points_raw[k]).0 <= 500 && 0 <= points_raw[k].1 <= 500,
        decreases n - i,
    {
        let p = points_raw[i];
        let mut v: Vec<i32> = Vec::new();
        v.push(p.0);
        v.push(p.1);
        assert(v.len() == 2);
        assert(v[0] == p.0);
        assert(v[1] == p.1);
        points.push(v);
        i = i + 1;
    }

    let mut queries: Vec<Vec<i32>> = Vec::new();
    let m = queries_raw.len();
    let mut j: usize = 0;
    while j < m
        invariant
            m == queries_raw.len(),
            j <= m,
            queries.len() == j,
            forall|k: int| 0 <= k < queries.len() ==> #[trigger] queries[k].len() == 3,
            forall|k: int| 0 <= k < queries.len() ==>
                #[trigger] queries[k][0] == queries_raw[k].0
                  && queries[k][1] == queries_raw[k].1
                  && queries[k][2] == queries_raw[k].2,
            forall|k: int| 0 <= k < queries_raw.len() ==>
                0 <= (#[trigger] queries_raw[k]).0 <= 500
                  && 0 <= queries_raw[k].1 <= 500
                  && 1 <= queries_raw[k].2 <= 500,
        decreases m - j,
    {
        let q = queries_raw[j];
        let mut v: Vec<i32> = Vec::new();
        v.push(q.0);
        v.push(q.1);
        v.push(q.2);
        assert(v.len() == 3);
        assert(v[0] == q.0);
        assert(v[1] == q.1);
        assert(v[2] == q.2);
        queries.push(v);
        j = j + 1;
    }

    (points, queries)
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(
    rng: &mut Rng,
    mode: usize,
    n: usize,
    m: usize,
) -> (Vec<(i32, i32)>, Vec<(i32, i32, i32)>) {
    let mut pts: Vec<(i32, i32)> = Vec::with_capacity(n);
    let mut qs: Vec<(i32, i32, i32)> = Vec::with_capacity(m);

    match mode {
        0 => {
            // random
            for _ in 0..n {
                pts.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500)));
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500), rng.gen_i32(1, 500)));
            }
        }
        1 => {
            // all points same
            let x = rng.gen_i32(0, 500);
            let y = rng.gen_i32(0, 500);
            for _ in 0..n {
                pts.push((x, y));
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500), rng.gen_i32(1, 500)));
            }
        }
        2 => {
            // corners
            for i in 0..n {
                let c = i % 4;
                let p = match c {
                    0 => (0, 0),
                    1 => (0, 500),
                    2 => (500, 0),
                    _ => (500, 500),
                };
                pts.push(p);
            }
            for _ in 0..m {
                qs.push((250, 250, 500));
            }
        }
        3 => {
            // tiny r=1 queries
            for _ in 0..n {
                pts.push((rng.gen_i32(0, 10), rng.gen_i32(0, 10)));
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 10), rng.gen_i32(0, 10), 1));
            }
        }
        4 => {
            // r=500 covers everything
            for _ in 0..n {
                pts.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500)));
            }
            for _ in 0..m {
                qs.push((250, 250, 500));
            }
        }
        5 => {
            // edge boundary cases
            for _ in 0..n {
                pts.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500)));
            }
            for _ in 0..m {
                let cx = rng.gen_i32(0, 500);
                let cy = rng.gen_i32(0, 500);
                qs.push((cx, cy, rng.gen_i32(1, 10)));
            }
        }
        6 => {
            // grid points
            let mut k = 0;
            for i in 0..n {
                let x = (i % 23) as i32 * 22;
                let y = ((i / 23) % 23) as i32 * 22;
                pts.push((x.min(500), y.min(500)));
                k += 1;
                if k > n { break; }
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500), rng.gen_i32(1, 500)));
            }
        }
        7 => {
            // zero-area edges, r=1
            for _ in 0..n {
                pts.push((0, 0));
            }
            for _ in 0..m {
                qs.push((0, 0, 1));
            }
        }
        8 => {
            // line points y=0
            for i in 0..n {
                pts.push(((i % 501) as i32, 0));
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 500), 0, rng.gen_i32(1, 500)));
            }
        }
        9 => {
            // max values
            for _ in 0..n {
                pts.push((500, 500));
            }
            for _ in 0..m {
                qs.push((0, 0, 500));
            }
        }
        _ => {
            for _ in 0..n {
                pts.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500)));
            }
            for _ in 0..m {
                qs.push((rng.gen_i32(0, 500), rng.gen_i32(0, 500), rng.gen_i32(1, 500)));
            }
        }
    }

    (pts, qs)
}

fn print_case(points: &Vec<Vec<i32>>, queries: &Vec<Vec<i32>>) {
    print!("{{\"points\":[");
    for i in 0..points.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", points[i][0], points[i][1]);
    }
    print!("],\"queries\":[");
    for j in 0..queries.len() {
        if j > 0 { print!(","); }
        print!("[{},{},{}]", queries[j][0], queries[j][1], queries[j][2]);
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
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_usize(1, 20),
            3 => rng.gen_usize(50, 100),
            4 => rng.gen_usize(200, 300),
            5 => 500,
            _ => rng.gen_usize(1, 500),
        };
        let m = match (t / 7) % 6 {
            0 => 1,
            1 => rng.gen_usize(1, 10),
            2 => rng.gen_usize(50, 150),
            3 => 500,
            4 => rng.gen_usize(1, 500),
            _ => rng.gen_usize(1, 100),
        };

        let (pts_raw, qs_raw) = build_case(&mut rng, mode, n, m);
        let (points, queries) = generate_test_case(&pts_raw, &qs_raw);
        print_case(&points, &queries);
    }
}