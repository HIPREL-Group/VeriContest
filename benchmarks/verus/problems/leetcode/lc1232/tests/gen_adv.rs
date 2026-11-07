use vstd::prelude::*;

verus! {
pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && -10000 <= p[0] && p[0] <= 10000 && -10000 <= p[1] && p[1] <= 10000
}

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> valid_pt(#[trigger] result[i]@),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> -10000 <= (#[trigger] result[i])[0] <= 10000 && -10000 <= result[i][1] <= 10000,
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
            forall|j: int| 0 <= j < result.len() ==> -10000 <= #[trigger] result[j][0] <= 10000 && -10000 <= result[j][1] <= 10000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { -10000 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { -10000 };
        let x = if x < -10000 { -10000 } else if x > 10000 { 10000 } else { x };
        let y = if y < -10000 { -10000 } else if y > 10000 { 10000 } else { y };
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
        p.push(-10000);
        p.push(-10000);
        fallback.push(p);
        let mut p = Vec::new();
        p.push(-10000);
        p.push(-9999);
        fallback.push(p);
        assert(fallback[0][1] != fallback[1][1]);
        assert(fallback[0]@ != fallback[1]@);
        fallback
    } else {
        assert forall|j: int| 0 <= j < result.len() implies valid_pt(#[trigger] result[j]@) by {
            assert(result[j].len() == 2);
            assert(-10000 <= result[j][0] <= 10000 && -10000 <= result[j][1] <= 10000);
        }
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
) -> (coords: Vec<Vec<i32>>)
    requires
        2 <= n <= 1000,
        xs.len() == n,
        ys.len() == n,
        forall |i: int| 0 <= i < n ==> -10000 <= #[trigger] xs[i] <= 10000,
        forall |i: int| 0 <= i < n ==> -10000 <= #[trigger] ys[i] <= 10000,
    ensures
        2 <= coords.len() <= 1000,
        forall |i: int| #![trigger coords[i]] 0 <= i < coords.len() ==> {
            &&& coords[i]@.len() == 2
            &&& -10000 <= coords[i]@[0] <= 10000
            &&& -10000 <= coords[i]@[1] <= 10000
        },
{
    let mut coords: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == xs.len(),
            n == ys.len(),
            2 <= n <= 1000,
            0 <= i <= n,
            coords.len() == i,
            forall |k: int| 0 <= k < n ==> -10000 <= #[trigger] xs[k] <= 10000,
            forall |k: int| 0 <= k < n ==> -10000 <= #[trigger] ys[k] <= 10000,
            forall |k: int| #![trigger coords[k]] 0 <= k < i as int ==> {
                &&& coords[k]@.len() == 2
                &&& coords[k]@[0] == xs[k]
                &&& coords[k]@[1] == ys[k]
            },
        decreases n - i,
    {
        let mut pt: Vec<i32> = Vec::new();
        pt.push(xs[i]);
        pt.push(ys[i]);
        assert(pt@.len() == 2);
        assert(pt@[0] == xs[i as int]);
        assert(pt@[1] == ys[i as int]);
        coords.push(pt);
        i = i + 1;
    }
    coords
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn clamp(v: i64) -> i32 {
    if v < -10000 {
        -10000
    } else if v > 10000 {
        10000
    } else {
        v as i32
    }
}

fn build_collinear(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    // Pick a line: y = m*x + b (in rationals), we pick two points and interpolate with distinct t
    let x0 = rng.gen_range_i32(-100, 100);
    let y0 = rng.gen_range_i32(-100, 100);
    let dx = rng.gen_range_i32(-20, 20);
    let dy = rng.gen_range_i32(-20, 20);
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    let mut used: std::collections::HashSet<(i32, i32)> = std::collections::HashSet::new();
    let mut t: i64 = 0;
    while xs.len() < n {
        let x = clamp(x0 as i64 + t * dx as i64);
        let y = clamp(y0 as i64 + t * dy as i64);
        if !used.contains(&(x, y)) {
            used.insert((x, y));
            xs.push(x);
            ys.push(y);
        }
        t += 1;
        if t > 100000 {
            // fallback: add random distinct points (may not be collinear but still valid inputs)
            let x = rng.gen_range_i32(-10000, 10000);
            let y = rng.gen_range_i32(-10000, 10000);
            if !used.contains(&(x, y)) {
                used.insert((x, y));
                xs.push(x);
                ys.push(y);
            }
        }
    }
    (xs, ys)
}

fn build_random(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    let mut used: std::collections::HashSet<(i32, i32)> = std::collections::HashSet::new();
    while xs.len() < n {
        let x = rng.gen_range_i32(-10000, 10000);
        let y = rng.gen_range_i32(-10000, 10000);
        if !used.contains(&(x, y)) {
            used.insert((x, y));
            xs.push(x);
            ys.push(y);
        }
    }
    (xs, ys)
}

fn build_collinear_with_outlier(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let (mut xs, mut ys) = build_collinear(rng, n);
    if n >= 3 {
        // perturb last point
        let idx = n - 1;
        let mut tries = 0;
        loop {
            let nx = clamp(xs[idx] as i64 + rng.gen_range_i32(-3, 3) as i64);
            let ny = clamp(ys[idx] as i64 + rng.gen_range_i32(1, 5) as i64);
            let mut dup = false;
            for k in 0..n {
                if k != idx && xs[k] == nx && ys[k] == ny {
                    dup = true;
                    break;
                }
            }
            if !dup {
                xs[idx] = nx;
                ys[idx] = ny;
                break;
            }
            tries += 1;
            if tries > 100 {
                break;
            }
        }
    }
    (xs, ys)
}

fn build_horizontal(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let y = rng.gen_range_i32(-10000, 10000);
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    let mut used: std::collections::HashSet<i32> = std::collections::HashSet::new();
    while xs.len() < n {
        let x = rng.gen_range_i32(-10000, 10000);
        if !used.contains(&x) {
            used.insert(x);
            xs.push(x);
            ys.push(y);
        }
    }
    (xs, ys)
}

fn build_vertical(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let x = rng.gen_range_i32(-10000, 10000);
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    let mut used: std::collections::HashSet<i32> = std::collections::HashSet::new();
    while xs.len() < n {
        let y = rng.gen_range_i32(-10000, 10000);
        if !used.contains(&y) {
            used.insert(y);
            xs.push(x);
            ys.push(y);
        }
    }
    (xs, ys)
}

fn build_diagonal(n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    for i in 0..n {
        xs.push(i as i32);
        ys.push(i as i32);
    }
    (xs, ys)
}

fn build_two_points(rng: &mut Rng) -> (Vec<i32>, Vec<i32>) {
    let x0 = rng.gen_range_i32(-10000, 10000);
    let y0 = rng.gen_range_i32(-10000, 10000);
    let mut x1 = rng.gen_range_i32(-10000, 10000);
    let mut y1 = rng.gen_range_i32(-10000, 10000);
    if x1 == x0 && y1 == y0 {
        x1 = if x0 < 10000 { x0 + 1 } else { x0 - 1 };
    }
    (vec![x0, x1], vec![y0, y1])
}

fn build_extreme(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    // points on line through extreme values
    let mut xs: Vec<i32> = Vec::new();
    let mut ys: Vec<i32> = Vec::new();
    let mut used: std::collections::HashSet<(i32, i32)> = std::collections::HashSet::new();
    let mut t: i32 = -10000;
    while xs.len() < n {
        let x = t;
        let y = t;
        if x >= -10000 && x <= 10000 && !used.contains(&(x, y)) {
            used.insert((x, y));
            xs.push(x);
            ys.push(y);
        }
        t += 1;
        if t > 10000 {
            // fallback random
            let x = rng.gen_range_i32(-10000, 10000);
            let y = rng.gen_range_i32(-10000, 10000);
            if !used.contains(&(x, y)) {
                used.insert((x, y));
                xs.push(x);
                ys.push(y);
            }
        }
    }
    (xs, ys)
}

fn print_json(coords: &Vec<Vec<i32>>) {
        let mut coords = coords.clone();
        coords.sort();
        let coords = generate_test_case(coords);
    print!("{{\"coordinates\":[");
    for i in 0..coords.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", coords[i][0], coords[i][1]);
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

    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => 2,
            1 => 3,
            2 => rng.gen_range_usize(2, 10),
            3 => rng.gen_range_usize(10, 100),
            4 => 1000,
            5 => rng.gen_range_usize(2, 1000),
            6 => rng.gen_range_usize(5, 50),
            7 => rng.gen_range_usize(2, 20),
            8 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(2, 1000),
        };

        let (xs, ys) = match mode {
            0 => build_two_points(&mut rng),
            1 => build_collinear(&mut rng, n),
            2 => build_collinear_with_outlier(&mut rng, n),
            3 => build_random(&mut rng, n),
            4 => build_collinear(&mut rng, n),
            5 => build_horizontal(&mut rng, n),
            6 => build_vertical(&mut rng, n),
            7 => build_diagonal(n),
            8 => build_extreme(&mut rng, n),
            _ => build_collinear_with_outlier(&mut rng, n),
        };

        let actual_n = xs.len();
        if actual_n < 2 || actual_n > 1000 {
            continue;
        }
        let coords = generate_candidate(actual_n, &xs, &ys);
        print_json(&coords);
    }
}
