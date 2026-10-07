use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    packages: Vec<i32>,
    boxes: Vec<Vec<i32>>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= packages.len() <= 100_000,
        forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
        1 <= boxes.len() <= 100_000,
        forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
        forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
            ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |j: int| #![trigger result.1@[j]] 0 <= j < result.1@.len() ==> 1 <= result.1@[j]@.len() <= 100_000,
        forall |j: int, k: int| 0 <= j < result.1@.len() && 0 <= k < result.1@[j]@.len()
            ==> 1 <= #[trigger] result.1@[j]@[k] <= 100_000,
{
    (packages, boxes)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn make_packages(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn make_boxes_supplier(rng: &mut Rng, sz: usize, lo: i32, hi: i32) -> Vec<i32> {
    // elements should be distinct per problem, but spec only requires 1..=100000
    use std::collections::HashSet;
    let mut seen = HashSet::new();
    let mut v = Vec::with_capacity(sz);
    let mut tries = 0;
    while v.len() < sz && tries < sz * 20 {
        let x = rng.gen_range_i32(lo, hi);
        if !seen.contains(&x) {
            seen.insert(x);
            v.push(x);
        }
        tries += 1;
    }
    // Fill rest if couldn't find distinct - just duplicate (spec allows this)
    while v.len() < sz {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn print_json(packages: &[i32], boxes: &[Vec<i32>]) {
    print!("{{\"packages\":[");
    for i in 0..packages.len() {
        if i > 0 { print!(","); }
        print!("{}", packages[i]);
    }
    print!("],\"boxes\":[");
    for j in 0..boxes.len() {
        if j > 0 { print!(","); }
        print!("[");
        for k in 0..boxes[j].len() {
            if k > 0 { print!(","); }
            print!("{}", boxes[j][k]);
        }
        print!("]");
    }
    println!("]}}");
}

fn build_case(rng: &mut Rng, mode: usize, iter: usize) -> (Vec<i32>, Vec<Vec<i32>>) {
    match mode {
        0 => {
            // tiny case
            let n = rng.gen_range_usize(1, 5);
            let m = rng.gen_range_usize(1, 3);
            let pkgs = make_packages(rng, n, 1, 20);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 5);
                bxs.push(make_boxes_supplier(rng, sz, 1, 30));
            }
            (pkgs, bxs)
        }
        1 => {
            // impossible-ish: small boxes, large packages
            let n = rng.gen_range_usize(3, 20);
            let m = rng.gen_range_usize(2, 5);
            let pkgs = make_packages(rng, n, 50, 100);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 10);
                bxs.push(make_boxes_supplier(rng, sz, 1, 40));
            }
            (pkgs, bxs)
        }
        2 => {
            // all same size packages
            let n = rng.gen_range_usize(5, 30);
            let v = rng.gen_range_i32(1, 100);
            let pkgs = vec![v; n];
            let m = rng.gen_range_usize(1, 5);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 10);
                bxs.push(make_boxes_supplier(rng, sz, 1, 200));
            }
            (pkgs, bxs)
        }
        3 => {
            // one supplier with exact fit
            let n = rng.gen_range_usize(3, 20);
            let pkgs = make_packages(rng, n, 1, 100);
            let mut bxs = Vec::new();
            bxs.push(make_boxes_supplier(rng, 5, 1, 100_000));
            bxs.push(vec![100_000]);
            (pkgs, bxs)
        }
        4 => {
            // edge: n=1
            let pkgs = vec![rng.gen_range_i32(1, 100_000)];
            let m = rng.gen_range_usize(1, 3);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 5);
                bxs.push(make_boxes_supplier(rng, sz, 1, 100_000));
            }
            (pkgs, bxs)
        }
        5 => {
            // max values
            let n = rng.gen_range_usize(1, 20);
            let pkgs = make_packages(rng, n, 99_990, 100_000);
            let mut bxs = Vec::new();
            bxs.push(vec![100_000]);
            bxs.push(make_boxes_supplier(rng, 10, 99_000, 100_000));
            (pkgs, bxs)
        }
        6 => {
            // min values
            let n = rng.gen_range_usize(1, 20);
            let pkgs = vec![1; n];
            let mut bxs = Vec::new();
            bxs.push(vec![1]);
            bxs.push(make_boxes_supplier(rng, 5, 1, 10));
            (pkgs, bxs)
        }
        7 => {
            // sorted packages
            let n = rng.gen_range_usize(10, 50);
            let mut pkgs = make_packages(rng, n, 1, 1000);
            pkgs.sort();
            let m = rng.gen_range_usize(2, 5);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(5, 20);
                bxs.push(make_boxes_supplier(rng, sz, 1, 1000));
            }
            (pkgs, bxs)
        }
        8 => {
            // large n
            let n = 1000;
            let pkgs = make_packages(rng, n, 1, 100_000);
            let m = rng.gen_range_usize(3, 10);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(10, 100);
                bxs.push(make_boxes_supplier(rng, sz, 1, 100_000));
            }
            (pkgs, bxs)
        }
        9 => {
            // many suppliers
            let n = rng.gen_range_usize(10, 100);
            let pkgs = make_packages(rng, n, 1, 10_000);
            let m = rng.gen_range_usize(50, 100);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 10);
                bxs.push(make_boxes_supplier(rng, sz, 1, 100_000));
            }
            (pkgs, bxs)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let m = rng.gen_range_usize(1, 10);
            let pkgs = make_packages(rng, n, 1, 100_000);
            let mut bxs = Vec::new();
            for _ in 0..m {
                let sz = rng.gen_range_usize(1, 20);
                bxs.push(make_boxes_supplier(rng, sz, 1, 100_000));
            }
            let _ = iter;
            (pkgs, bxs)
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (pkgs, bxs) = build_case(&mut rng, mode, t);
        let (pkgs, bxs) = generate_test_case(pkgs, bxs);
        print_json(&pkgs, &bxs);
    }
}