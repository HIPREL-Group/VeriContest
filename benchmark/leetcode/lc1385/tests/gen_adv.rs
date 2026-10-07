use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 500 { 500usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 500, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -1000 <= #[trigger] result[j] <= 1000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { -1000 };
        result.push(if value < -1000 { -1000 } else if value > 1000 { 1000 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(arr1: Vec<i32>, arr2: Vec<i32>, d: i32) -> (result: (Vec<i32>, Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1.len() <= 500,
        0 <= result.2 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> -1000 <= #[trigger] result.1[i] <= 1000,
{
    (bounded_values(&arr1), bounded_values(&arr2), if d < 0 { 0 } else if d > 100 { 100 } else { d })
}


pub fn generate_candidate(
    arr1: Vec<i32>,
    arr2: Vec<i32>,
    d: i32,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= arr1.len() <= 500,
        1 <= arr2.len() <= 500,
        0 <= d <= 100,
        forall|i: int| 0 <= i < arr1.len() ==> -1000 <= #[trigger] arr1[i] <= 1000,
        forall|j: int| 0 <= j < arr2.len() ==> -1000 <= #[trigger] arr2[j] <= 1000,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1.len() <= 500,
        0 <= result.2 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall|j: int| 0 <= j < result.1.len() ==> -1000 <= #[trigger] result.1[j] <= 1000,
{
    (arr1, arr2, d)
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

fn make_arr(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_constant(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn build_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, i32) {
    match mode {
        0 => {
            // tiny random
            let n1 = rng.gen_range_usize(1, 5);
            let n2 = rng.gen_range_usize(1, 5);
            let d = rng.gen_range_i32(0, 10);
            (make_arr(rng, n1, -20, 20), make_arr(rng, n2, -20, 20), d)
        }
        1 => {
            // d = 0
            let n1 = rng.gen_range_usize(1, 50);
            let n2 = rng.gen_range_usize(1, 50);
            (make_arr(rng, n1, -1000, 1000), make_arr(rng, n2, -1000, 1000), 0)
        }
        2 => {
            // d = 100, max
            let n1 = rng.gen_range_usize(1, 100);
            let n2 = rng.gen_range_usize(1, 100);
            (make_arr(rng, n1, -1000, 1000), make_arr(rng, n2, -1000, 1000), 100)
        }
        3 => {
            // arr1 single element
            let n2 = rng.gen_range_usize(1, 500);
            let d = rng.gen_range_i32(0, 100);
            let mut a = Vec::new();
            a.push(rng.gen_range_i32(-1000, 1000));
            (a, make_arr(rng, n2, -1000, 1000), d)
        }
        4 => {
            // arr2 single element
            let n1 = rng.gen_range_usize(1, 500);
            let d = rng.gen_range_i32(0, 100);
            let mut b = Vec::new();
            b.push(rng.gen_range_i32(-1000, 1000));
            (make_arr(rng, n1, -1000, 1000), b, d)
        }
        5 => {
            // both at extremes
            let n1 = rng.gen_range_usize(1, 500);
            let n2 = rng.gen_range_usize(1, 500);
            let mut a = Vec::with_capacity(n1);
            let mut b = Vec::with_capacity(n2);
            for _ in 0..n1 { a.push(if rng.next_u64() % 2 == 0 { -1000 } else { 1000 }); }
            for _ in 0..n2 { b.push(if rng.next_u64() % 2 == 0 { -1000 } else { 1000 }); }
            (a, b, rng.gen_range_i32(0, 100))
        }
        6 => {
            // identical arrays
            let n = rng.gen_range_usize(1, 200);
            let a = make_arr(rng, n, -1000, 1000);
            let b = a.clone();
            (a, b, rng.gen_range_i32(0, 100))
        }
        7 => {
            // far apart - arr1 negative, arr2 positive
            let n1 = rng.gen_range_usize(1, 200);
            let n2 = rng.gen_range_usize(1, 200);
            (make_arr(rng, n1, -1000, -500), make_arr(rng, n2, 500, 1000), rng.gen_range_i32(0, 100))
        }
        8 => {
            // constants
            let n1 = rng.gen_range_usize(1, 100);
            let n2 = rng.gen_range_usize(1, 100);
            let v1 = rng.gen_range_i32(-1000, 1000);
            let v2 = rng.gen_range_i32(-1000, 1000);
            (make_constant(n1, v1), make_constant(n2, v2), rng.gen_range_i32(0, 100))
        }
        9 => {
            // max sizes
            (make_arr(rng, 500, -1000, 1000), make_arr(rng, 500, -1000, 1000), rng.gen_range_i32(0, 100))
        }
        10 => {
            // boundary distance: arr1 at v, arr2 at v+d+1 (just outside)
            let d = rng.gen_range_i32(0, 100);
            let n1 = rng.gen_range_usize(1, 100);
            let n2 = rng.gen_range_usize(1, 100);
            let base = rng.gen_range_i32(-500, 500);
            let mut a = Vec::with_capacity(n1);
            let mut b = Vec::with_capacity(n2);
            for _ in 0..n1 { a.push(base); }
            for _ in 0..n2 { b.push(base + d + 1); }
            (a, b, d)
        }
        _ => {
            // medium random
            let n1 = rng.gen_range_usize(1, 500);
            let n2 = rng.gen_range_usize(1, 500);
            (make_arr(rng, n1, -1000, 1000), make_arr(rng, n2, -1000, 1000), rng.gen_range_i32(0, 100))
        }
    }
}

fn print_json(arr1: &[i32], arr2: &[i32], d: i32) {
        let (arr1, arr2, d) = generate_test_case(arr1.to_vec(), arr2.to_vec(), d);
    print!("{{\"arr1\":[");
    for i in 0..arr1.len() {
        if i > 0 { print!(","); }
        print!("{}", arr1[i]);
    }
    print!("],\"arr2\":[");
    for i in 0..arr2.len() {
        if i > 0 { print!(","); }
        print!("{}", arr2[i]);
    }
    println!("],\"d\":{}}}", d);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b, d) = build_test(&mut rng, mode);
        let (a2, b2, d2) = generate_candidate(a, b, d);
        print_json(&a2, &b2, d2);
    }
}
