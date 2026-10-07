use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    a_vals: &Vec<i32>,
    b_vals: &Vec<i32>,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100_000,
        a_vals.len() == n,
        b_vals.len() == n,
        forall |i: int| 0 <= i < n ==> 1 <= #[trigger] a_vals[i] <= 100,
        forall |i: int| 0 <= i < n ==> 1 <= #[trigger] b_vals[i] <= 100,
    ensures
        res.0.len() == res.1.len(),
        1 <= res.0.len() <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 100,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 100,
{
    let mut av: Vec<i32> = Vec::new();
    let mut bv: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100_000,
            a_vals.len() == n,
            b_vals.len() == n,
            av.len() == i,
            bv.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] av[k] == a_vals[k],
            forall |k: int| 0 <= k < i as int ==> #[trigger] bv[k] == b_vals[k],
            forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] a_vals[k] <= 100,
            forall |k: int| 0 <= k < n as int ==> 1 <= #[trigger] b_vals[k] <= 100,
        decreases n - i,
    {
        av.push(a_vals[i]);
        bv.push(b_vals[i]);
        i = i + 1;
    }
    (av, bv)
}

}

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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut b: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all equal
            for _ in 0..n {
                a.push(50);
                b.push(50);
            }
        }
        1 => {
            // alice values high, bob values low
            for _ in 0..n {
                a.push(100);
                b.push(1);
            }
        }
        2 => {
            // bob values high, alice values low
            for _ in 0..n {
                a.push(1);
                b.push(100);
            }
        }
        3 => {
            // random small
            for _ in 0..n {
                a.push(rng.gen_range_i32(1, 5));
                b.push(rng.gen_range_i32(1, 5));
            }
        }
        4 => {
            // random full range
            for _ in 0..n {
                a.push(rng.gen_range_i32(1, 100));
                b.push(rng.gen_range_i32(1, 100));
            }
        }
        5 => {
            // opposing extremes
            for i in 0..n {
                if i % 2 == 0 {
                    a.push(100);
                    b.push(1);
                } else {
                    a.push(1);
                    b.push(100);
                }
            }
        }
        6 => {
            // same values
            for _ in 0..n {
                let v = rng.gen_range_i32(1, 100);
                a.push(v);
                b.push(v);
            }
        }
        7 => {
            // sum=constant (a+b=101)
            for _ in 0..n {
                let v = rng.gen_range_i32(1, 100);
                a.push(v);
                b.push(101 - v);
            }
        }
        8 => {
            // boundary values
            for _ in 0..n {
                let av = if rng.next_u64() % 2 == 0 { 1 } else { 100 };
                let bv = if rng.next_u64() % 2 == 0 { 1 } else { 100 };
                a.push(av);
                b.push(bv);
            }
        }
        9 => {
            // ascending
            for i in 0..n {
                let v = ((i % 100) + 1) as i32;
                a.push(v);
                b.push(101 - v);
            }
        }
        _ => {
            for _ in 0..n {
                a.push(rng.gen_range_i32(1, 100));
                b.push(rng.gen_range_i32(1, 100));
            }
        }
    }
    (a, b)
}

fn print_json(a: &[i32], b: &[i32]) {
    print!("{{\"alice_values\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    print!("],\"bob_values\":[");
    for i in 0..b.len() {
        if i > 0 { print!(","); }
        print!("{}", b[i]);
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
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3 + (t % 10),
            3 => 50 + (t % 50),
            4 => 500 + (t % 100),
            5 => 10_000,
            _ => 100_000,
        };
        let (a, b) = build_case(&mut rng, mode, n);
        let (av, bv) = generate_test_case(n, &a, &b);
        print_json(&av, &bv);
    }
}