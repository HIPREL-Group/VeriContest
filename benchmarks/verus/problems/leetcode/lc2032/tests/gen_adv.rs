use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n1: usize,
    n2: usize,
    n3: usize,
    vals1: &Vec<i32>,
    vals2: &Vec<i32>,
    vals3: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>))
    requires
        1 <= n1 <= 100,
        1 <= n2 <= 100,
        1 <= n3 <= 100,
        vals1.len() == n1,
        vals2.len() == n2,
        vals3.len() == n3,
        forall|i: int| 0 <= i < vals1.len() ==> 1 <= #[trigger] vals1[i] <= 100,
        forall|i: int| 0 <= i < vals2.len() ==> 1 <= #[trigger] vals2[i] <= 100,
        forall|i: int| 0 <= i < vals3.len() ==> 1 <= #[trigger] vals3[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.1.len() <= 100,
        1 <= result.2.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 100,
{
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut c: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n1
        invariant
            i <= n1,
            a.len() == i,
            vals1.len() == n1,
            forall|k: int| 0 <= k < vals1.len() ==> 1 <= #[trigger] vals1[k] <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 100,
        decreases n1 - i,
    {
        a.push(vals1[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n2
        invariant
            j <= n2,
            b.len() == j,
            vals2.len() == n2,
            forall|k: int| 0 <= k < vals2.len() ==> 1 <= #[trigger] vals2[k] <= 100,
            forall|k: int| 0 <= k < b.len() ==> 1 <= #[trigger] b[k] <= 100,
        decreases n2 - j,
    {
        b.push(vals2[j]);
        j = j + 1;
    }

    let mut k: usize = 0;
    while k < n3
        invariant
            k <= n3,
            c.len() == k,
            vals3.len() == n3,
            forall|t: int| 0 <= t < vals3.len() ==> 1 <= #[trigger] vals3[t] <= 100,
            forall|t: int| 0 <= t < c.len() ==> 1 <= #[trigger] c[t] <= 100,
        decreases n3 - k,
    {
        c.push(vals3[k]);
        k = k + 1;
    }

    (a, b, c)
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

    fn gen_val(&mut self) -> i32 {
        self.gen_range_usize(1, 100) as i32
    }
}

fn make_vec(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_val());
    }
    v
}

fn make_const_vec(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn make_range_vec(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let mut x = start + i as i32;
        if x < 1 { x = 1; }
        if x > 100 { x = 100; }
        v.push(x);
    }
    v
}

fn print_json(n1: &Vec<i32>, n2: &Vec<i32>, n3: &Vec<i32>) {
    fn arr(v: &Vec<i32>) -> String {
        let mut s = String::from("[");
        for i in 0..v.len() {
            if i > 0 { s.push(','); }
            s.push_str(&v[i].to_string());
        }
        s.push(']');
        s
    }
    println!("{{\"nums1\":{},\"nums2\":{},\"nums3\":{}}}", arr(n1), arr(n2), arr(n3));
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // Small random
            let n1 = rng.gen_range_usize(1, 5);
            let n2 = rng.gen_range_usize(1, 5);
            let n3 = rng.gen_range_usize(1, 5);
            (make_vec(rng, n1), make_vec(rng, n2), make_vec(rng, n3))
        }
        1 => {
            // All same value across arrays
            let v = rng.gen_range_usize(1, 100) as i32;
            (make_const_vec(50, v), make_const_vec(50, v), make_const_vec(50, v))
        }
        2 => {
            // Disjoint ranges
            (make_range_vec(30, 1), make_range_vec(30, 34), make_range_vec(30, 67))
        }
        3 => {
            // Two overlap, third disjoint
            let v = 50i32;
            let mut a = make_const_vec(20, v);
            a.append(&mut make_range_vec(10, 1));
            let mut b = make_const_vec(20, v);
            b.append(&mut make_range_vec(10, 11));
            let c = make_range_vec(30, 70);
            (a, b, c)
        }
        4 => {
            // Maximum size
            (make_vec(rng, 100), make_vec(rng, 100), make_vec(rng, 100))
        }
        5 => {
            // Minimum size
            (vec![rng.gen_val()], vec![rng.gen_val()], vec![rng.gen_val()])
        }
        6 => {
            // Singletons with overlap
            let v = rng.gen_range_usize(1, 100) as i32;
            (vec![v], vec![v], vec![(v % 100) + 1])
        }
        7 => {
            // Duplicates within a single array
            let v = rng.gen_val();
            (make_const_vec(100, v), make_vec(rng, 50), make_vec(rng, 50))
        }
        8 => {
            // Boundary values
            let n1 = rng.gen_range_usize(1, 100);
            let n2 = rng.gen_range_usize(1, 100);
            let n3 = rng.gen_range_usize(1, 100);
            let mut a = Vec::new();
            let mut b = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n1 { a.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 }); }
            for _ in 0..n2 { b.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 }); }
            for _ in 0..n3 { c.push(if rng.next_u64() % 2 == 0 { 1 } else { 100 }); }
            (a, b, c)
        }
        9 => {
            // Each value appears in exactly two arrays
            let a: Vec<i32> = (1..=30).collect();
            let b: Vec<i32> = (20..=50).collect();
            let c: Vec<i32> = (40..=70).collect();
            (a, b, c)
        }
        _ => {
            let n1 = rng.gen_range_usize(1, 100);
            let n2 = rng.gen_range_usize(1, 100);
            let n3 = rng.gen_range_usize(1, 100);
            let _ = t;
            (make_vec(rng, n1), make_vec(rng, n2), make_vec(rng, n3))
        }
    }
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
        let (v1, v2, v3) = gen_mode(&mut rng, mode, t);
        let n1 = v1.len();
        let n2 = v2.len();
        let n3 = v3.len();
        // Safety clamps (should already hold).
        if n1 < 1 || n1 > 100 || n2 < 1 || n2 > 100 || n3 < 1 || n3 > 100 {
            continue;
        }
        let mut ok = true;
        for &x in &v1 { if x < 1 || x > 100 { ok = false; } }
        for &x in &v2 { if x < 1 || x > 100 { ok = false; } }
        for &x in &v3 { if x < 1 || x > 100 { ok = false; } }
        if !ok { continue; }

        let (a, b, c) = generate_test_case(n1, n2, n3, &v1, &v2, &v3);
        print_json(&a, &b, &c);
    }
}