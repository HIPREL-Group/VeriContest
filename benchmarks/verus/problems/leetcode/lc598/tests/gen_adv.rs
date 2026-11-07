use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    a_vals: &Vec<i32>,
    b_vals: &Vec<i32>,
) -> (result: (i32, i32, Vec<Vec<i32>>))
    requires
        1 <= m <= 40000,
        1 <= n <= 40000,
        a_vals.len() == b_vals.len(),
        a_vals.len() <= 10_000,
        forall|i: int| 0 <= i < a_vals.len() ==> 1 <= #[trigger] a_vals[i] <= m,
        forall|i: int| 0 <= i < b_vals.len() ==> 1 <= #[trigger] b_vals[i] <= n,
    ensures
        result.0 == m,
        result.1 == n,
        result.0 >= 1,
        result.1 >= 1,
        result.0 <= 40000,
        result.1 <= 40000,
        0 <= result.2@.len() <= 10_000,
        forall|i: int| 0 <= i < result.2@.len() ==> (#[trigger] result.2@[i]).len() == 2,
        forall|i: int| 0 <= i < result.2@.len() ==>
            1 <= (#[trigger] result.2@[i])@[0] && result.2@[i]@[0] <= m &&
            1 <= result.2@[i]@[1] && result.2@[i]@[1] <= n,
{
    let mut ops: Vec<Vec<i32>> = Vec::new();
    let len = a_vals.len();
    let mut i: usize = 0;

    while i < len
        invariant
            len == a_vals.len(),
            len == b_vals.len(),
            len <= 10_000,
            0 <= i <= len,
            ops.len() == i,
            forall|k: int| 0 <= k < a_vals.len() ==> 1 <= #[trigger] a_vals[k] <= m,
            forall|k: int| 0 <= k < b_vals.len() ==> 1 <= #[trigger] b_vals[k] <= n,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] ops@[k]).len() == 2,
            forall|k: int| 0 <= k < i as int ==>
                1 <= (#[trigger] ops@[k])@[0] && ops@[k]@[0] <= m &&
                1 <= ops@[k]@[1] && ops@[k]@[1] <= n,
        decreases len - i,
    {
        let a = a_vals[i];
        let b = b_vals[i];
        let mut pair: Vec<i32> = Vec::new();
        pair.push(a);
        pair.push(b);
        assert(pair.len() == 2);
        assert(pair@[0] == a);
        assert(pair@[1] == b);
        ops.push(pair);
        i = i + 1;
    }

    (m, n, ops)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_case(mode: usize, rng: &mut Rng) -> (i32, i32, Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // small m,n, empty ops
            let m = rng.gen_range_i32(1, 10);
            let n = rng.gen_range_i32(1, 10);
            (m, n, vec![], vec![])
        }
        1 => {
            // single op
            let m = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_i32(1, 100);
            let a = rng.gen_range_i32(1, m);
            let b = rng.gen_range_i32(1, n);
            (m, n, vec![a], vec![b])
        }
        2 => {
            // max m,n, many ops
            let m = 40000;
            let n = 40000;
            let k = 10_000usize;
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(rng.gen_range_i32(1, m));
                b.push(rng.gen_range_i32(1, n));
            }
            (m, n, a, b)
        }
        3 => {
            // all ops are (m,n) -> max is all cells = k
            let m = rng.gen_range_i32(1, 1000);
            let n = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_usize(1, 100);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(m);
                b.push(n);
            }
            (m, n, a, b)
        }
        4 => {
            // all ops are (1,1) -> min is 1
            let m = rng.gen_range_i32(1, 1000);
            let n = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_usize(1, 100);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(1);
                b.push(1);
            }
            (m, n, a, b)
        }
        5 => {
            // m=1,n=1
            let k = rng.gen_range_usize(0, 100);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(1);
                b.push(1);
            }
            (1, 1, a, b)
        }
        6 => {
            // m=1
            let n = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_usize(0, 100);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(1);
                b.push(rng.gen_range_i32(1, n));
            }
            (1, n, a, b)
        }
        7 => {
            // n=1
            let m = rng.gen_range_i32(1, 1000);
            let k = rng.gen_range_usize(0, 100);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(rng.gen_range_i32(1, m));
                b.push(1);
            }
            (m, 1, a, b)
        }
        8 => {
            // boundary - one op with (1,1)
            let m = rng.gen_range_i32(2, 40000);
            let n = rng.gen_range_i32(2, 40000);
            (m, n, vec![1], vec![1])
        }
        9 => {
            // mix including (m,n)
            let m = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_i32(1, 100);
            let k = rng.gen_range_usize(1, 50);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                if rng.next_u64() % 2 == 0 {
                    a.push(m);
                    b.push(n);
                } else {
                    a.push(rng.gen_range_i32(1, m));
                    b.push(rng.gen_range_i32(1, n));
                }
            }
            (m, n, a, b)
        }
        _ => {
            // random
            let m = rng.gen_range_i32(1, 40000);
            let n = rng.gen_range_i32(1, 40000);
            let k = rng.gen_range_usize(0, 200);
            let mut a = Vec::with_capacity(k);
            let mut b = Vec::with_capacity(k);
            for _ in 0..k {
                a.push(rng.gen_range_i32(1, m));
                b.push(rng.gen_range_i32(1, n));
            }
            (m, n, a, b)
        }
    }
}

fn print_json(m: i32, n: i32, ops: &Vec<Vec<i32>>) {
    print!("{{\"m\":{},\"n\":{},\"ops\":[", m, n);
    for i in 0..ops.len() {
        if i > 0 {
            print!(",");
        }
        print!("[");
        for j in 0..ops[i].len() {
            if j > 0 {
                print!(",");
            }
            print!("{}", ops[i][j]);
        }
        print!("]");
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
        let (m, n, a_vals, b_vals) = build_case(mode, &mut rng);
        let (mm, nn, ops) = generate_test_case(m, n, &a_vals, &b_vals);
        print_json(mm, nn, &ops);
    }
}