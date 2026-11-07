use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    x: i32,
    y: i32,
    pts_flat: &Vec<i32>,
    n: usize,
) -> (points: Vec<Vec<i32>>)
    requires
        1 <= x <= 10000,
        1 <= y <= 10000,
        1 <= n <= 10000,
        pts_flat.len() == 2 * n,
        forall|i: int| 0 <= i < pts_flat.len() ==> 1 <= #[trigger] pts_flat[i] <= 10000,
    ensures
        1 <= points.len() <= 10000,
        points.len() == n,
        forall|i: int| 0 <= i < points.len() ==>
            (#[trigger] points[i]).len() == 2
            && 1 <= points[i][0] && points[i][0] <= 10000
            && 1 <= points[i][1] && points[i][1] <= 10000,
        forall|i: int| #![trigger points[i]@.len()]
            0 <= i < points.len() ==>
            points[i]@.len() == 2
            && 1 <= points[i]@[0] && points[i]@[0] <= 10000
            && 1 <= points[i]@[1] && points[i]@[1] <= 10000,
{
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n >= 1,
            n <= 10000,
            k <= n,
            points.len() == k,
            pts_flat.len() == 2 * n,
            forall|i: int| 0 <= i < pts_flat.len() ==> 1 <= #[trigger] pts_flat[i] <= 10000,
            forall|i: int| 0 <= i < points.len() ==>
                (#[trigger] points[i]).len() == 2
                && 1 <= points[i][0] && points[i][0] <= 10000
                && 1 <= points[i][1] && points[i][1] <= 10000,
        decreases n - k,
    {
        let a = pts_flat[2 * k];
        let b = pts_flat[2 * k + 1];
        let mut p: Vec<i32> = Vec::new();
        p.push(a);
        p.push(b);
        assert(p.len() == 2);
        assert(p[0] == a);
        assert(p[1] == b);
        points.push(p);
        k = k + 1;
    }

    proof {
        assert forall|i: int| 0 <= i < points.len() implies
            points[i]@.len() == 2
            && 1 <= points[i]@[0] && points[i]@[0] <= 10000
            && 1 <= points[i]@[1] && points[i]@[1] <= 10000
        by {
            assert(points[i].len() == 2);
            assert(points[i]@.len() == points[i].len());
            assert(points[i]@[0] == points[i][0]);
            assert(points[i]@[1] == points[i][1]);
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
        Self { state: if seed == 0 { 1 } else { seed } }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_flat(n: usize, pairs: Vec<(i32, i32)>) -> Vec<i32> {
    let mut out = Vec::with_capacity(2 * n);
    for (a, b) in pairs {
        out.push(a);
        out.push(b);
    }
    out
}

fn gen_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, i32, usize, Vec<i32>) {
    let x = rng.gen_range_i32(1, 10000);
    let y = rng.gen_range_i32(1, 10000);

    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 10000,
        3 => rng.gen_range_usize(1, 20),
        4 => rng.gen_range_usize(50, 500),
        5 => rng.gen_range_usize(1, 100),
        6 => rng.gen_range_usize(1, 100),
        7 => rng.gen_range_usize(1, 100),
        8 => rng.gen_range_usize(1, 100),
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 1000),
    };

    let mut pairs: Vec<(i32, i32)> = Vec::with_capacity(n);
    for _ in 0..n {
        let (a, b) = match mode {
            // No valid points
            3 => {
                let mut a = rng.gen_range_i32(1, 10000);
                let mut b = rng.gen_range_i32(1, 10000);
                if a == x { a = if a == 1 { 2 } else { a - 1 }; }
                if b == y { b = if b == 1 { 2 } else { b - 1 }; }
                (a, b)
            }
            // All points same x
            5 => (x, rng.gen_range_i32(1, 10000)),
            // All points same y
            6 => (rng.gen_range_i32(1, 10000), y),
            // Point at exact location
            7 => (x, y),
            // Mix valid and invalid
            8 => {
                if rng.next_u64() % 2 == 0 {
                    if rng.next_u64() % 2 == 0 {
                        (x, rng.gen_range_i32(1, 10000))
                    } else {
                        (rng.gen_range_i32(1, 10000), y)
                    }
                } else {
                    (rng.gen_range_i32(1, 10000), rng.gen_range_i32(1, 10000))
                }
            }
            // Boundary coords
            9 => {
                let choices_a = [1i32, 10000, x];
                let choices_b = [1i32, 10000, y];
                let a = choices_a[(rng.next_u64() as usize) % 3];
                let b = choices_b[(rng.next_u64() as usize) % 3];
                (a, b)
            }
            _ => (rng.gen_range_i32(1, 10000), rng.gen_range_i32(1, 10000)),
        };
        pairs.push((a, b));
    }

    let flat = build_flat(n, pairs);
    let _ = t;
    (x, y, n, flat)
}

fn print_json(x: i32, y: i32, flat: &[i32], n: usize) {
    print!("{{\"x\":{},\"y\":{},\"points\":[", x, y);
    for i in 0..n {
        if i > 0 { print!(","); }
        print!("[{},{}]", flat[2 * i], flat[2 * i + 1]);
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
        let (x, y, n, flat) = gen_case(&mut rng, mode, t);
        let points = generate_test_case(x, y, &flat, n);
        let _ = points;
        print_json(x, y, &flat, n);
    }
}