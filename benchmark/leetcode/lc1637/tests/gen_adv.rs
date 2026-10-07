use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    xs: &Vec<i32>,
    ys: &Vec<i32>,
) -> (points: Vec<Vec<i32>>)
    requires
        2 <= n <= 100_000,
        xs.len() == n,
        ys.len() == n,
        forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] xs[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] ys[i] <= 1_000_000_000,
    ensures
        2 <= points.len() <= 100_000,
        forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
            points@[i]@.len() == 2,
        forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
            0 <= points@[i]@[0] <= 1_000_000_000,
        forall|i: int| #![trigger points@[i]] 0 <= i < points@.len() ==>
            0 <= points@[i]@[1] <= 1_000_000_000,
{
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            2 <= n <= 100_000,
            xs.len() == n,
            ys.len() == n,
            0 <= i <= n,
            points.len() == i,
            forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] xs[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < n as int ==> 0 <= #[trigger] ys[k] <= 1_000_000_000,
            forall|k: int| #![trigger points@[k]] 0 <= k < i as int ==>
                points@[k]@.len() == 2,
            forall|k: int| #![trigger points@[k]] 0 <= k < i as int ==>
                0 <= points@[k]@[0] <= 1_000_000_000,
            forall|k: int| #![trigger points@[k]] 0 <= k < i as int ==>
                0 <= points@[k]@[1] <= 1_000_000_000,
        decreases n - i,
    {
        let mut p: Vec<i32> = Vec::new();
        p.push(xs[i]);
        p.push(ys[i]);
        assert(p@.len() == 2);
        assert(p@[0] == xs[i as int]);
        assert(p@[1] == ys[i as int]);
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

fn build_case(mode: usize, rng: &mut Rng) -> (usize, Vec<i32>, Vec<i32>) {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => rng.gen_range_usize(2, 10),
        3 => rng.gen_range_usize(10, 100),
        4 => rng.gen_range_usize(100, 1000),
        5 => 100_000,
        6 => rng.gen_range_usize(1000, 10000),
        7 => rng.gen_range_usize(2, 50),
        8 => rng.gen_range_usize(2, 50),
        9 => rng.gen_range_usize(2, 50),
        _ => rng.gen_range_usize(2, 500),
    };

    let mut xs: Vec<i32> = Vec::with_capacity(n);
    let mut ys: Vec<i32> = Vec::with_capacity(n);

    match mode {
        5 | 6 => {
            // Large: random x, y full range
            for _ in 0..n {
                xs.push(rng.gen_range_i32(0, 1_000_000_000));
                ys.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        7 => {
            // All x identical
            let xv = rng.gen_range_i32(0, 1_000_000_000);
            for _ in 0..n {
                xs.push(xv);
                ys.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        8 => {
            // Extreme values
            for i in 0..n {
                let v = if i % 2 == 0 { 0 } else { 1_000_000_000 };
                xs.push(v);
                ys.push(if i % 3 == 0 { 0 } else { 1_000_000_000 });
            }
        }
        9 => {
            // Sequential x
            for i in 0..n {
                xs.push(i as i32);
                ys.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        0 | 1 => {
            for _ in 0..n {
                xs.push(rng.gen_range_i32(0, 1_000_000_000));
                ys.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        _ => {
            for _ in 0..n {
                xs.push(rng.gen_range_i32(0, 1_000_000_000));
                ys.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
    }

    (n, xs, ys)
}

fn print_json(points: &Vec<Vec<i32>>) {
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, xs, ys) = build_case(mode, &mut rng);
        let points = generate_test_case(n, &xs, &ys);
        print_json(&points);
    }
}