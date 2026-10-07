use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    target_vals: &Vec<i32>,
    arr_vals: &Vec<i32>,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        target_vals.len() == arr_vals.len(),
        1 <= target_vals.len() <= 1000,
        forall |i: int| 0 <= i < target_vals.len() ==> 1 <= #[trigger] target_vals[i] <= 1000,
        forall |i: int| 0 <= i < arr_vals.len() ==> 1 <= #[trigger] arr_vals[i] <= 1000,
    ensures
        res.0.len() == res.1.len(),
        1 <= res.0.len() <= 1000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1000,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 1000,
{
    let n = target_vals.len();
    let mut t: Vec<i32> = Vec::new();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == target_vals.len(),
            n == arr_vals.len(),
            1 <= n <= 1000,
            0 <= i <= n,
            t.len() == i,
            a.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] t[k] == target_vals[k],
            forall |k: int| 0 <= k < i as int ==> #[trigger] a[k] == arr_vals[k],
            forall |k: int| 0 <= k < target_vals.len() ==> 1 <= #[trigger] target_vals[k] <= 1000,
            forall |k: int| 0 <= k < arr_vals.len() ==> 1 <= #[trigger] arr_vals[k] <= 1000,
        decreases n - i,
    {
        t.push(target_vals[i]);
        a.push(arr_vals[i]);
        i += 1;
    }

    assert(forall |k: int| 0 <= k < t.len() ==> #[trigger] t[k] == target_vals[k]);
    assert(forall |k: int| 0 <= k < a.len() ==> #[trigger] a[k] == arr_vals[k]);

    (t, a)
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_random(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    let mut a = Vec::with_capacity(n);
    for _ in 0..n {
        t.push(rng.gen_range_i32(1, 1000));
        a.push(rng.gen_range_i32(1, 1000));
    }
    (t, a)
}

fn build_equal(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        t.push(rng.gen_range_i32(1, 1000));
    }
    let a = t.clone();
    (t, a)
}

fn build_permutation(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        t.push(rng.gen_range_i32(1, 1000));
    }
    let mut a = t.clone();
    // shuffle a
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        a.swap(i, j);
    }
    (t, a)
}

fn build_off_by_one(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let (t, mut a) = build_permutation(rng, n);
    if n > 0 {
        let idx = rng.gen_range_usize(0, n - 1);
        let cur = a[idx];
        let newv = if cur == 1000 { 1 } else { cur + 1 };
        a[idx] = newv;
    }
    (t, a)
}

fn build_reversed(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        t.push(rng.gen_range_i32(1, 1000));
    }
    let mut a = t.clone();
    a.reverse();
    (t, a)
}

fn build_all_same(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let v = rng.gen_range_i32(1, 1000);
    let t = vec![v; n];
    let a = vec![v; n];
    (t, a)
}

fn build_almost_same(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let v = rng.gen_range_i32(1, 999);
    let t = vec![v; n];
    let mut a = vec![v; n];
    if n > 0 {
        let idx = rng.gen_range_usize(0, n - 1);
        a[idx] = v + 1;
    }
    (t, a)
}

fn build_extremes(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    let mut a = Vec::with_capacity(n);
    for _ in 0..n {
        let v = if rng.next_u64() % 2 == 0 { 1 } else { 1000 };
        t.push(v);
    }
    a = t.clone();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        a.swap(i, j);
    }
    (t, a)
}

fn build_missing_value(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        t.push(rng.gen_range_i32(1, 500));
    }
    let mut a = t.clone();
    if n >= 2 {
        a[0] = 600;
        a[1] = 700;
    } else if n == 1 {
        a[0] = if t[0] == 1000 { 1 } else { t[0] + 1 };
    }
    (t, a)
}

fn build_swap_count(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    // Same multiset but different ordering with duplicates
    let mut t = Vec::with_capacity(n);
    for i in 0..n {
        t.push(((i % 5) as i32) + 1);
    }
    let mut a = t.clone();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        a.swap(i, j);
    }
    let _ = rng;
    (t, a)
}

fn print_json(t: &[i32], a: &[i32]) {
    print!("{{\"target\":[");
    for i in 0..t.len() {
        if i > 0 { print!(","); }
        print!("{}", t[i]);
    }
    print!("],\"arr\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 1000,
            2 => 2 + (t % 50),
            3 => if t % 2 == 0 { 1 } else { 1000 },
            4 => 100 + (t % 50),
            5 => 1,
            6 => 500,
            7 => 250 + (t % 100),
            8 => 50,
            _ => 10 + (t % 20),
        };
        let n = if n < 1 { 1 } else if n > 1000 { 1000 } else { n };

        let (tv, av) = match mode {
            0 => build_random(&mut rng, n),
            1 => build_equal(&mut rng, n),
            2 => build_permutation(&mut rng, n),
            3 => build_off_by_one(&mut rng, n),
            4 => build_reversed(&mut rng, n),
            5 => build_all_same(&mut rng, n),
            6 => build_almost_same(&mut rng, n),
            7 => build_extremes(&mut rng, n),
            8 => build_missing_value(&mut rng, n),
            _ => build_swap_count(&mut rng, n),
        };

        let (tt, aa) = generate_test_case(&tv, &av);
        print_json(&tt, &aa);
    }
}