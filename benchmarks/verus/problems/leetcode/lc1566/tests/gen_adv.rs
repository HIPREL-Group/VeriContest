use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr_vals: &Vec<i32>,
    m_val: i32,
    k_val: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        2 <= arr_vals.len() <= 100,
        forall |i: int| 0 <= i < arr_vals.len() ==> 1 <= #[trigger] arr_vals[i] <= 100,
        1 <= m_val <= 100,
        2 <= k_val <= 100,
    ensures
        2 <= res.0.len() <= 100,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100,
        1 <= res.1 <= 100,
        2 <= res.2 <= 100,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr_vals.len()
        invariant
            0 <= i <= arr_vals.len(),
            out.len() == i,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] out[j] <= 100,
            forall |j: int| 0 <= j < i as int ==> out[j] == arr_vals[j],
            forall |j: int| 0 <= j < arr_vals.len() ==> 1 <= #[trigger] arr_vals[j] <= 100,
        decreases arr_vals.len() - i,
    {
        out.push(arr_vals[i]);
        i += 1;
    }
    (out, m_val, k_val)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn build_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // simple repeated pattern, repeat exactly k times
            let m = rng.gen_range(1, 5) as i32;
            let k = rng.gen_range(2, 5) as i32;
            let mut arr: Vec<i32> = Vec::new();
            let pat: Vec<i32> = (0..m).map(|_| rng.gen_range(1, 10) as i32).collect();
            for _ in 0..k {
                for &v in &pat { arr.push(v); }
            }
            // pad to length >= 2
            while arr.len() < 2 { arr.push(1); }
            while arr.len() > 100 { arr.pop(); }
            if arr.len() < 2 { arr.push(1); }
            (arr, m, k)
        }
        1 => {
            // all same value
            let n = rng.gen_range(2, 100) as usize;
            let v = rng.gen_range(1, 100) as i32;
            let arr: Vec<i32> = (0..n).map(|_| v).collect();
            let m = rng.gen_range(1, (n as i64).min(50)) as i32;
            let k = rng.gen_range(2, 100) as i32;
            (arr, m, k)
        }
        2 => {
            // random array
            let n = rng.gen_range(2, 100) as usize;
            let arr: Vec<i32> = (0..n).map(|_| rng.gen_range(1, 100) as i32).collect();
            let m = rng.gen_range(1, 100) as i32;
            let k = rng.gen_range(2, 100) as i32;
            (arr, m, k)
        }
        3 => {
            // small alphabet
            let n = rng.gen_range(2, 100) as usize;
            let arr: Vec<i32> = (0..n).map(|_| rng.gen_range(1, 3) as i32).collect();
            let m = rng.gen_range(1, 10) as i32;
            let k = rng.gen_range(2, 10) as i32;
            (arr, m, k)
        }
        4 => {
            // pattern with noise before/after
            let m = rng.gen_range(1, 4) as i32;
            let k = rng.gen_range(2, 4) as i32;
            let mut arr: Vec<i32> = Vec::new();
            let prefix = rng.gen_range(0, 5) as usize;
            for _ in 0..prefix { arr.push(rng.gen_range(1, 10) as i32); }
            let pat: Vec<i32> = (0..m).map(|_| rng.gen_range(1, 10) as i32).collect();
            for _ in 0..k { for &v in &pat { arr.push(v); } }
            let suffix = rng.gen_range(0, 5) as usize;
            for _ in 0..suffix { arr.push(rng.gen_range(1, 10) as i32); }
            while arr.len() < 2 { arr.push(1); }
            while arr.len() > 100 { arr.pop(); }
            if arr.len() < 2 { arr.push(1); }
            (arr, m, k)
        }
        5 => {
            // maximum size
            let n = 100usize;
            let arr: Vec<i32> = (0..n).map(|i| ((i % 10) + 1) as i32).collect();
            let m = 10i32;
            let k = 10i32;
            (arr, m, k)
        }
        6 => {
            // minimum size
            let arr = vec![1i32, 1];
            (arr, 1, 2)
        }
        7 => {
            // m larger than usable pattern
            let n = rng.gen_range(2, 50) as usize;
            let arr: Vec<i32> = (0..n).map(|_| rng.gen_range(1, 5) as i32).collect();
            let m = rng.gen_range(50, 100) as i32;
            let k = rng.gen_range(2, 100) as i32;
            (arr, m, k)
        }
        8 => {
            // pattern exactly k-1 times (should be false for k)
            let m = rng.gen_range(1, 4) as i32;
            let k = rng.gen_range(3, 5) as i32;
            let rep = k - 1;
            let mut arr: Vec<i32> = Vec::new();
            let pat: Vec<i32> = (0..m).map(|_| rng.gen_range(1, 5) as i32).collect();
            for _ in 0..rep { for &v in &pat { arr.push(v); } }
            arr.push(99);
            while arr.len() < 2 { arr.push(1); }
            while arr.len() > 100 { arr.pop(); }
            if arr.len() < 2 { arr.push(1); }
            (arr, m, k)
        }
        9 => {
            // alternating
            let n = rng.gen_range(2, 100) as usize;
            let arr: Vec<i32> = (0..n).map(|i| if i % 2 == 0 { 1i32 } else { 2i32 }).collect();
            let m = rng.gen_range(1, 5) as i32;
            let k = rng.gen_range(2, 10) as i32;
            (arr, m, k)
        }
        _ => {
            let arr = vec![1i32, 2, 4, 4, 4, 4];
            (arr, 1, 3)
        }
    }
}

fn sanitize(arr: Vec<i32>, m: i32, k: i32) -> (Vec<i32>, i32, i32) {
    let mut a = arr;
    if a.len() < 2 { while a.len() < 2 { a.push(1); } }
    if a.len() > 100 { a.truncate(100); }
    for v in a.iter_mut() {
        if *v < 1 { *v = 1; }
        if *v > 100 { *v = 100; }
    }
    let mm = if m < 1 { 1 } else if m > 100 { 100 } else { m };
    let kk = if k < 2 { 2 } else if k > 100 { 100 } else { k };
    (a, mm, kk)
}

fn print_json(arr: &[i32], m: i32, k: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"m\":{},\"k\":{}}}", m, k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (arr, m, k) = build_case(mode, &mut rng);
        let (arr, m, k) = sanitize(arr, m, k);
        let (out_arr, out_m, out_k) = generate_test_case(&arr, m, k);
        print_json(&out_arr, out_m, out_k);
    }
}