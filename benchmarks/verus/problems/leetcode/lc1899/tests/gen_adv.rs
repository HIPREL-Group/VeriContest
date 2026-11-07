use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    tx: i32,
    ty: i32,
    tz: i32,
    a_vals: &Vec<i32>,
    b_vals: &Vec<i32>,
    c_vals: &Vec<i32>,
) -> (result: (Vec<Vec<i32>>, Vec<i32>))
    requires
        1 <= n <= 100_000,
        a_vals.len() == n,
        b_vals.len() == n,
        c_vals.len() == n,
        1 <= tx <= 1000,
        1 <= ty <= 1000,
        1 <= tz <= 1000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a_vals[i] <= 1000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] b_vals[i] <= 1000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] c_vals[i] <= 1000,
    ensures
        1 <= result.0.len() <= 100_000,
        result.1.len() == 3,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 3,
        forall|i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() ==> 1 <= #[trigger] result.0[i][j] <= 1000,
        forall|j: int| 0 <= j < 3 ==> 1 <= #[trigger] result.1[j] <= 1000,
{
    let mut triplets: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            0 <= idx <= n,
            triplets.len() == idx,
            a_vals.len() == n,
            b_vals.len() == n,
            c_vals.len() == n,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a_vals[i] <= 1000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] b_vals[i] <= 1000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] c_vals[i] <= 1000,
            forall|i: int| 0 <= i < idx as int ==> #[trigger] triplets[i].len() == 3,
            forall|i: int, j: int| 0 <= i < idx as int && 0 <= j < 3 ==> 1 <= #[trigger] triplets[i][j] <= 1000,
        decreases n - idx,
    {
        let mut t: Vec<i32> = Vec::new();
        t.push(a_vals[idx]);
        t.push(b_vals[idx]);
        t.push(c_vals[idx]);
        assert(t.len() == 3);
        assert(t[0] == a_vals[idx as int]);
        assert(t[1] == b_vals[idx as int]);
        assert(t[2] == c_vals[idx as int]);
        triplets.push(t);
        assert(triplets[idx as int].len() == 3);
        idx = idx + 1;
    }

    let mut target: Vec<i32> = Vec::new();
    target.push(tx);
    target.push(ty);
    target.push(tz);

    (triplets, target)
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

fn build_case(rng: &mut Rng, mode: usize) -> (usize, i32, i32, i32, Vec<i32>, Vec<i32>, Vec<i32>) {
    // Choose n
    let n: usize = match mode {
        0 => rng.gen_range_usize(1, 5),
        1 => 1,
        2 => 2,
        3 => rng.gen_range_usize(10, 50),
        4 => rng.gen_range_usize(100, 500),
        5 => rng.gen_range_usize(1000, 2000),
        6 => rng.gen_range_usize(10, 100),
        7 => rng.gen_range_usize(3, 20),
        8 => rng.gen_range_usize(5, 30),
        9 => rng.gen_range_usize(5, 50),
        _ => rng.gen_range_usize(1, 100),
    };

    let tx = rng.gen_range_i32(1, 1000);
    let ty = rng.gen_range_i32(1, 1000);
    let tz = rng.gen_range_i32(1, 1000);

    let mut a_vals: Vec<i32> = Vec::with_capacity(n);
    let mut b_vals: Vec<i32> = Vec::with_capacity(n);
    let mut c_vals: Vec<i32> = Vec::with_capacity(n);

    for _ in 0..n {
        let (a, b, c) = match mode {
            0 => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
            1 => (tx, ty, tz),
            2 => {
                // all equal to target
                (tx, ty, tz)
            }
            3 => {
                // values all <= target components
                let a = rng.gen_range_i32(1, tx);
                let b = rng.gen_range_i32(1, ty);
                let c = rng.gen_range_i32(1, tz);
                (a, b, c)
            }
            4 => {
                // all values > 500
                (rng.gen_range_i32(500, 1000), rng.gen_range_i32(500, 1000), rng.gen_range_i32(500, 1000))
            }
            5 => {
                // many triplets some match each coordinate exactly
                let r = rng.gen_range_usize(0, 3);
                if r == 0 {
                    (tx, rng.gen_range_i32(1, ty), rng.gen_range_i32(1, tz))
                } else if r == 1 {
                    (rng.gen_range_i32(1, tx), ty, rng.gen_range_i32(1, tz))
                } else if r == 2 {
                    (rng.gen_range_i32(1, tx), rng.gen_range_i32(1, ty), tz)
                } else {
                    (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000))
                }
            }
            6 => {
                // one coordinate always exceeds target
                (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000), 1000)
            }
            7 => {
                // all 1s
                (1, 1, 1)
            }
            8 => {
                // all 1000s
                (1000, 1000, 1000)
            }
            9 => {
                // close-to-target triplets
                let a = if tx > 1 { rng.gen_range_i32(tx - 1, std::cmp::min(tx + 1, 1000)) } else { rng.gen_range_i32(1, 2) };
                let b = if ty > 1 { rng.gen_range_i32(ty - 1, std::cmp::min(ty + 1, 1000)) } else { rng.gen_range_i32(1, 2) };
                let c = if tz > 1 { rng.gen_range_i32(tz - 1, std::cmp::min(tz + 1, 1000)) } else { rng.gen_range_i32(1, 2) };
                (a, b, c)
            }
            _ => (rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
        };
        a_vals.push(a);
        b_vals.push(b);
        c_vals.push(c);
    }

    (n, tx, ty, tz, a_vals, b_vals, c_vals)
}

fn print_json(triplets: &Vec<Vec<i32>>, target: &Vec<i32>) {
    print!("{{\"triplets\":[");
    for i in 0..triplets.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..triplets[i].len() {
            if j > 0 { print!(","); }
            print!("{}", triplets[i][j]);
        }
        print!("]");
    }
    print!("],\"target\":[");
    for i in 0..target.len() {
        if i > 0 { print!(","); }
        print!("{}", target[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, tx, ty, tz, a_vals, b_vals, c_vals) = build_case(&mut rng, mode);
        let (triplets, target) = generate_test_case(n, tx, ty, tz, &a_vals, &b_vals, &c_vals);
        print_json(&triplets, &target);
    }
}