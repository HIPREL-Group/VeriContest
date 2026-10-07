use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    xs: &Vec<i32>,
    ys: &Vec<i32>,
) -> (points: Vec<Vec<i32>>)
    requires
        1 <= xs.len() <= 100,
        xs.len() == ys.len(),
        forall|i: int| 0 <= i < xs.len() ==> -1000 <= #[trigger] xs[i] <= 1000,
        forall|i: int| 0 <= i < ys.len() ==> -1000 <= #[trigger] ys[i] <= 1000,
    ensures
        1 <= points.len() <= 100,
        forall|i: int| 0 <= i < points.len() ==>
            (#[trigger] points[i]).len() == 2
            && -1000 <= points[i][0] <= 1000
            && -1000 <= points[i][1] <= 1000,
{
    let n = xs.len();
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == xs.len(),
            xs.len() == ys.len(),
            1 <= n <= 100,
            0 <= i <= n,
            points.len() == i,
            forall|k: int| 0 <= k < xs.len() ==> -1000 <= #[trigger] xs[k] <= 1000,
            forall|k: int| 0 <= k < ys.len() ==> -1000 <= #[trigger] ys[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] points[k]).len() == 2
                && points[k][0] == xs[k]
                && points[k][1] == ys[k],
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_from_vecs(xs: Vec<i32>, ys: Vec<i32>) -> Vec<Vec<i32>> {
    generate_test_case(&xs, &ys)
}

fn make_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // single point
            let x = rng.gen_i32(-1000, 1000);
            let y = rng.gen_i32(-1000, 1000);
            (vec![x], vec![y])
        }
        1 => {
            // two points same
            let x = rng.gen_i32(-1000, 1000);
            let y = rng.gen_i32(-1000, 1000);
            (vec![x, x], vec![y, y])
        }
        2 => {
            // extreme corners
            (vec![-1000, 1000, -1000, 1000], vec![-1000, 1000, 1000, -1000])
        }
        3 => {
            // all zeros
            let n = rng.gen_usize(1, 100);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(0);
                ys.push(0);
            }
            (xs, ys)
        }
        4 => {
            // collinear horizontal
            let n = rng.gen_usize(2, 100);
            let y = rng.gen_i32(-1000, 1000);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(rng.gen_i32(-1000, 1000));
                ys.push(y);
            }
            (xs, ys)
        }
        5 => {
            // collinear vertical
            let n = rng.gen_usize(2, 100);
            let x = rng.gen_i32(-1000, 1000);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(x);
                ys.push(rng.gen_i32(-1000, 1000));
            }
            (xs, ys)
        }
        6 => {
            // diagonal line
            let n = rng.gen_usize(2, 100);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for i in 0..n {
                let v = (i as i32) - 50;
                let v = if v < -1000 { -1000 } else if v > 1000 { 1000 } else { v };
                xs.push(v);
                ys.push(v);
            }
            (xs, ys)
        }
        7 => {
            // maximum size 100
            let n = 100usize;
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(rng.gen_i32(-1000, 1000));
                ys.push(rng.gen_i32(-1000, 1000));
            }
            (xs, ys)
        }
        8 => {
            // alternating extreme
            let n = rng.gen_usize(2, 100);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for i in 0..n {
                if i % 2 == 0 {
                    xs.push(-1000);
                    ys.push(-1000);
                } else {
                    xs.push(1000);
                    ys.push(1000);
                }
            }
            (xs, ys)
        }
        9 => {
            // small random
            let n = rng.gen_usize(1, 10);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(rng.gen_i32(-10, 10));
                ys.push(rng.gen_i32(-10, 10));
            }
            (xs, ys)
        }
        _ => {
            let n = rng.gen_usize(1, 100);
            let mut xs = Vec::new();
            let mut ys = Vec::new();
            for _ in 0..n {
                xs.push(rng.gen_i32(-1000, 1000));
                ys.push(rng.gen_i32(-1000, 1000));
            }
            (xs, ys)
        }
    }
}

fn print_json(points: &Vec<Vec<i32>>) {
    print!("{{\"points\":[");
    for i in 0..points.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..points[i].len() {
            if j > 0 { print!(","); }
            print!("{}", points[i][j]);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (xs, ys) = make_case(&mut rng, mode);
        let points = build_from_vecs(xs, ys);
        print_json(&points);
    }
}