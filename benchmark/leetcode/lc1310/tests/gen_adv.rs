use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr_vals: &Vec<i32>,
    queries_l: &Vec<i32>,
    queries_r: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= arr_vals.len() <= 30_000,
        1 <= queries_l.len() <= 30_000,
        queries_l.len() == queries_r.len(),
        forall |i: int| 0 <= i < arr_vals.len() ==> 1 <= #[trigger] arr_vals[i] <= 1_000_000_000,
        forall |k: int| 0 <= k < queries_l.len() ==>
            0 <= #[trigger] queries_l[k] <= queries_r[k] < arr_vals.len() as i32,
    ensures
        ({
            let (arr, queries) = result;
            &&& 1 <= arr.len() <= 30_000
            &&& 1 <= queries.len() <= 30_000
            &&& (forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000)
            &&& (forall |k: int|
                0 <= k < queries.len() ==> #[trigger] queries[k].len() == 2
                    && 0 <= queries[k][0] <= queries[k][1] < arr.len() as i32)
        }),
{
    let n = arr_vals.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == arr_vals.len(),
            i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] arr[k] == arr_vals[k],
            forall |k: int| 0 <= k < arr_vals.len() ==> 1 <= #[trigger] arr_vals[k] <= 1_000_000_000,
        decreases n - i,
    {
        arr.push(arr_vals[i]);
        i += 1;
    }

    let q = queries_l.len();
    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < q
        invariant
            q == queries_l.len(),
            q == queries_r.len(),
            j <= q,
            queries.len() == j,
            arr.len() == n,
            1 <= n <= 30_000,
            forall |k: int| 0 <= k < j as int ==> #[trigger] queries[k].len() == 2
                && queries[k][0] == queries_l[k]
                && queries[k][1] == queries_r[k],
            forall |k: int| 0 <= k < q as int ==>
                0 <= #[trigger] queries_l[k] <= queries_r[k] < arr_vals.len() as i32,
            n == arr_vals.len(),
        decreases q - j,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(queries_l[j]);
        pair.push(queries_r[j]);
        assert(pair.len() == 2);
        assert(pair[0] == queries_l[j as int]);
        assert(pair[1] == queries_r[j as int]);
        queries.push(pair);
        j += 1;
    }

    (arr, queries)
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

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let (n, q) = match mode {
        0 => (1usize, 1usize),
        1 => (1, 10),
        2 => (2, 5),
        3 => (10, 10),
        4 => (100, 100),
        5 => (30_000, 100),
        6 => (100, 30_000),
        7 => (30_000, 30_000),
        8 => (5, 30_000),
        9 => (500, 500),
        _ => (rng.gen_range_usize(1, 200), rng.gen_range_usize(1, 200)),
    };

    let mut arr = Vec::with_capacity(n);
    for _ in 0..n {
        let v = match mode {
            3 => 1,
            4 => rng.gen_range_i32(1, 10),
            5 => 1_000_000_000,
            7 => rng.gen_range_i32(1, 1_000_000_000),
            _ => rng.gen_range_i32(1, 1_000_000_000),
        };
        arr.push(v);
    }

    let mut ql = Vec::with_capacity(q);
    let mut qr = Vec::with_capacity(q);
    for _ in 0..q {
        let a = rng.gen_range_usize(0, n - 1);
        let b = rng.gen_range_usize(0, n - 1);
        let (l, r) = if a <= b { (a, b) } else { (b, a) };
        ql.push(l as i32);
        qr.push(r as i32);
    }

    // Adversarial tweaks
    if mode == 0 && q >= 1 {
        ql[0] = 0;
        qr[0] = 0;
    }
    if mode == 8 {
        for k in 0..q {
            ql[k] = 0;
            qr[k] = (n - 1) as i32;
        }
    }

    (arr, ql, qr)
}

fn print_json(arr: &[i32], ql: &[i32], qr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    print!("],\"queries\":[");
    for i in 0..ql.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", ql[i], qr[i]);
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
        let (arr_vals, ql, qr) = make_test(&mut rng, mode);
        let (arr, queries) = generate_test_case(&arr_vals, &ql, &qr);
        // Rebuild ql/qr for printing
        let mut pl = Vec::with_capacity(queries.len());
        let mut pr = Vec::with_capacity(queries.len());
        for q in &queries {
            pl.push(q[0]);
            pr.push(q[1]);
        }
        print_json(&arr, &pl, &pr);
    }
}