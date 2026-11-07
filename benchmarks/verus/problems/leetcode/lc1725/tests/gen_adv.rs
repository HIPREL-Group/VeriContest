use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 1000000000 && 1 <= result[i][1] <= 1000000000,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result[i])[0] != result[i][1],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;

    while i < count
        invariant
            1 <= count <= 1000, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 1000000000 && 1 <= result[j][1] <= 1000000000,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j][0] != result[j][1],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 1000000000 { 1000000000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 1000000000 { 1000000000 } else { b };
        if a == b { b = if a < 1000000000 { a + 1 } else { 1 }; }
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    dims: &Vec<(i32, i32)>,
) -> (res: Vec<Vec<i32>>)
    requires
        1 <= dims.len() <= 1000,
        forall |i: int| 0 <= i < dims.len() ==>
            1 <= (#[trigger] dims[i]).0 <= 1_000_000_000,
        forall |i: int| 0 <= i < dims.len() ==>
            1 <= (#[trigger] dims[i]).1 <= 1_000_000_000,
    ensures
        1 <= res.len() <= 1000,
        res.len() == dims.len(),
        forall |i: int| 0 <= i < res.len() ==>
            (#[trigger] res[i]).len() == 2,
        forall |i: int| 0 <= i < res.len() ==>
            1 <= (#[trigger] res[i])[0] <= 1_000_000_000,
        forall |i: int| 0 <= i < res.len() ==>
            1 <= (#[trigger] res[i])[1] <= 1_000_000_000,
{
    let n = dims.len();
    let mut res: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == dims.len(),
            1 <= n <= 1000,
            0 <= i <= n,
            res.len() == i,
            forall |k: int| 0 <= k < dims.len() ==>
                1 <= (#[trigger] dims[k]).0 <= 1_000_000_000,
            forall |k: int| 0 <= k < dims.len() ==>
                1 <= (#[trigger] dims[k]).1 <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==>
                (#[trigger] res[k]).len() == 2,
            forall |k: int| 0 <= k < i as int ==>
                1 <= (#[trigger] res[k])[0] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==>
                1 <= (#[trigger] res[k])[1] <= 1_000_000_000,
        decreases n - i,
    {
        let (l, w) = dims[i];
        let mut pair: Vec<i32> = Vec::new();
        pair.push(l);
        pair.push(w);
        assert(pair.len() == 2);
        assert(pair[0] == l);
        assert(pair[1] == w);
        res.push(pair);
        i = i + 1;
    }

    res
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
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

fn make_dim(rng: &mut Rng, lo: i32, hi: i32) -> (i32, i32) {
    let a = rng.gen_range_i32(lo, hi);
    let mut b = rng.gen_range_i32(lo, hi);
    if b == a {
        if b < 1_000_000_000 {
            b += 1;
        } else {
            b -= 1;
        }
    }
    (a, b)
}

fn gen_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<(i32, i32)> {
    let mut v: Vec<(i32, i32)> = Vec::with_capacity(n);
    match mode {
        0 => {
            // small values
            for _ in 0..n {
                v.push(make_dim(rng, 1, 10));
            }
        }
        1 => {
            // all dims same side length
            let k = rng.gen_range_i32(1, 1_000_000_000);
            for _ in 0..n {
                let other_lo = if k < 1_000_000_000 { k + 1 } else { 1 };
                let other = rng.gen_range_i32(other_lo, 1_000_000_000);
                // put k as min
                let (l, w) = if rng.next_u64() % 2 == 0 { (k, other) } else { (other, k) };
                v.push((l, w));
            }
        }
        2 => {
            // one element
            v.push(make_dim(rng, 1, 1_000_000_000));
        }
        3 => {
            // max sides
            for _ in 0..n {
                let a = rng.gen_range_i32(999_999_990, 1_000_000_000);
                let mut b = rng.gen_range_i32(999_999_990, 1_000_000_000);
                if b == a {
                    if b > 1 { b -= 1; } else { b += 1; }
                }
                v.push((a, b));
            }
        }
        4 => {
            // min sides
            for _ in 0..n {
                let a = 1;
                let b = rng.gen_range_i32(2, 100);
                v.push((a, b));
            }
        }
        5 => {
            // only one with max side
            let k = 1_000_000_000;
            for _ in 0..n {
                let a = rng.gen_range_i32(1, 100);
                let b = rng.gen_range_i32(101, 1000);
                v.push((a, b));
            }
            if n > 0 {
                v[0] = (k, if k > 1 { k - 1 } else { 2 });
            }
        }
        6 => {
            // all rectangles have side 1 as min
            for _ in 0..n {
                let b = rng.gen_range_i32(2, 1_000_000_000);
                v.push((1, b));
            }
        }
        7 => {
            // random across full range
            for _ in 0..n {
                v.push(make_dim(rng, 1, 1_000_000_000));
            }
        }
        8 => {
            // two distinct max squares
            for i in 0..n {
                if i % 2 == 0 {
                    v.push((5, 10));
                } else {
                    v.push((7, 20));
                }
            }
        }
        9 => {
            // increasing sides
            for i in 0..n {
                let s = ((i as i32) % 1000) + 1;
                let o = if s < 1_000_000_000 { s + 1 } else { 1 };
                v.push((s, o));
            }
        }
        _ => {
            for _ in 0..n {
                v.push(make_dim(rng, 1, 1_000_000_000));
            }
        }
    }
    // ensure length == n
    while v.len() < n {
        v.push(make_dim(rng, 1, 1_000_000_000));
    }
    v.truncate(n);
    // ensure all are valid
    for i in 0..v.len() {
        let (a, b) = v[i];
        let a2 = if a < 1 { 1 } else if a > 1_000_000_000 { 1_000_000_000 } else { a };
        let b2 = if b < 1 { 1 } else if b > 1_000_000_000 { 1_000_000_000 } else { b };
        let b3 = if a2 == b2 {
            if b2 < 1_000_000_000 { b2 + 1 } else { b2 - 1 }
        } else { b2 };
        v[i] = (a2, b3);
    }
    v
}

fn print_json(rects: &Vec<Vec<i32>>) {
    let rects = generate_test_case(rects.to_vec());
    print!("{{\"rectangles\":[");
    for i in 0..rects.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", rects[i][0], rects[i][1]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 5 + (t % 10),
            2 => 1,
            3 => 1000,
            4 => 10 + (t % 50),
            5 => 50 + (t % 100),
            6 => 1000,
            7 => 1 + (rng.next_u64() as usize % 1000),
            8 => 100 + (t % 200),
            9 => 500,
            _ => 100,
        };
        let n = if n == 0 { 1 } else if n > 1000 { 1000 } else { n };

        let dims = gen_mode(&mut rng, mode, n);
        let rects = generate_candidate(&dims);
        print_json(&rects);
    }
}
