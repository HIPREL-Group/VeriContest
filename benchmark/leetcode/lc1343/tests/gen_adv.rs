use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 10000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 10000 { 10000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(arr: Vec<i32>, k: i32, threshold: i32) -> (result: (Vec<i32>, i32, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        1 <= result.1 <= result.0.len(),
        0 <= result.2 <= 10000,
{
    let arr = bounded_values(&arr);
    let k = if k < 1 { 1 } else if k as usize > arr.len() { arr.len() as i32 } else { k };
    let threshold = if threshold < 0 { 0 } else if threshold > 10000 { 10000 } else { threshold };
    (arr, k, threshold)
}


pub fn generate_candidate(
    n: usize,
    k_val: i32,
    threshold_val: i32,
    values: &Vec<i32>,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= n,
        n <= 100_000,
        1 <= k_val,
        k_val as int <= n as int,
        0 <= threshold_val,
        threshold_val <= 10_000,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 10_000,
    ensures
        1 <= res.0.len(),
        res.0.len() <= 100_000,
        1 <= res.1,
        res.1 as usize <= res.0.len(),
        forall |i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 10_000,
        0 <= res.2,
        res.2 <= 10_000,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            arr.len() == i,
            forall |j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 10_000,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] arr[j] <= 10_000,
            forall |j: int| 0 <= j < i as int ==> arr[j] == values[j],
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= v <= 10_000);
        arr.push(v);
        i = i + 1;
        assert(arr[i as int - 1] == v);
        assert(forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] arr[j] <= 10_000) by {
            assert(forall |j: int| 0 <= j < (i as int - 1) ==> arr[j] == values[j]);
        }
    }

    (arr, k_val, threshold_val)
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build(rng: &mut Rng, mode: usize, tcase: usize) -> (Vec<i32>, i32, i32) {
    let (n, k, threshold, vals) = match mode {
        0 => {
            // minimal: n=1, k=1
            (1usize, 1i32, rng.gen_i32(0, 10_000), vec![rng.gen_i32(0, 10_000)])
        }
        1 => {
            // small n=k
            let n = rng.gen_usize(2, 10);
            let k = n as i32;
            let t = rng.gen_i32(0, 10_000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            (n, k, t, v)
        }
        2 => {
            // all zeros
            let n = rng.gen_usize(1, 100);
            let k = rng.gen_usize(1, n) as i32;
            let t = 0i32;
            let v = vec![0i32; n];
            (n, k, t, v)
        }
        3 => {
            // all max
            let n = rng.gen_usize(1, 100);
            let k = rng.gen_usize(1, n) as i32;
            let t = 10_000i32;
            let v = vec![10_000i32; n];
            (n, k, t, v)
        }
        4 => {
            // example 1
            let v = vec![2,2,2,2,5,5,5,8];
            (8usize, 3i32, 4i32, v)
        }
        5 => {
            // example 2
            let v = vec![11,13,17,23,29,31,7,5,2,3];
            (10usize, 3i32, 5i32, v)
        }
        6 => {
            // k=1
            let n = rng.gen_usize(1, 1000);
            let t = rng.gen_i32(0, 10_000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            (n, 1i32, t, v)
        }
        7 => {
            // large n
            let n = 100_000usize;
            let k = rng.gen_usize(1, n) as i32;
            let t = rng.gen_i32(0, 10_000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            (n, k, t, v)
        }
        8 => {
            // threshold at boundary
            let n = rng.gen_usize(10, 200);
            let k = rng.gen_usize(1, n) as i32;
            let t = if tcase % 2 == 0 { 0i32 } else { 10_000i32 };
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            (n, k, t, v)
        }
        9 => {
            // alternating
            let n = rng.gen_usize(2, 500);
            let k = rng.gen_usize(1, n) as i32;
            let t = rng.gen_i32(0, 10_000);
            let mut v = Vec::new();
            for i in 0..n { v.push(if i % 2 == 0 { 0 } else { 10_000 }); }
            (n, k, t, v)
        }
        _ => {
            let n = rng.gen_usize(1, 500);
            let k = rng.gen_usize(1, n) as i32;
            let t = rng.gen_i32(0, 10_000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_i32(0, 10_000)); }
            (n, k, t, v)
        }
    };

    let (arr, kk, tt) = generate_candidate(n, k, threshold, &vals);
    (arr, kk, tt)
}

fn print_json(arr: &[i32], k: i32, threshold: i32) {
    let (arr, k, threshold) = generate_test_case(arr.to_vec(), k, threshold);
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"k\":{},\"threshold\":{}}}", k, threshold);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (arr, k, threshold) = build(&mut rng, mode, t);
        print_json(&arr, k, threshold);
    }
}
