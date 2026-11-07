use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, b: Vec<i32>) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= a.len() <= 1000,
        1 <= b.len() <= 1000,
        forall |i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1000,
        forall |i: int| 0 <= i < b.len() ==> 0 <= #[trigger] b[i] <= 1000,
    ensures
        1 <= res.0.len() <= 1000,
        1 <= res.1.len() <= 1000,
        forall |i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 1000,
        forall |i: int| 0 <= i < res.1.len() ==> 0 <= #[trigger] res.1[i] <= 1000,
{
    (a, b)
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_vec(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn filled_vec(len: usize, value: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(value);
    }
    v
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
    }
    println!("]}}");
}

fn make_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // small random
            let la = rng.gen_range_usize(1, 10);
            let lb = rng.gen_range_usize(1, 10);
            let a = make_vec(rng, la, 0, 5);
            let b = make_vec(rng, lb, 0, 5);
            (a, b)
        }
        1 => {
            // large max
            let a = make_vec(rng, 1000, 0, 1000);
            let b = make_vec(rng, 1000, 0, 1000);
            (a, b)
        }
        2 => {
            // singletons
            let v1 = rng.gen_range_i32(0, 1000);
            let v2 = rng.gen_range_i32(0, 1000);
            (vec![v1], vec![v2])
        }
        3 => {
            // identical arrays
            let la = rng.gen_range_usize(1, 100);
            let a = make_vec(rng, la, 0, 20);
            let b = a.clone();
            (a, b)
        }
        4 => {
            // disjoint ranges
            let la = rng.gen_range_usize(1, 500);
            let lb = rng.gen_range_usize(1, 500);
            let a = make_vec(rng, la, 0, 499);
            let b = make_vec(rng, lb, 500, 1000);
            (a, b)
        }
        5 => {
            // all zeros
            let la = rng.gen_range_usize(1, 1000);
            let lb = rng.gen_range_usize(1, 1000);
            (filled_vec(la, 0), filled_vec(lb, 0))
        }
        6 => {
            // all max value
            let la = rng.gen_range_usize(1, 1000);
            let lb = rng.gen_range_usize(1, 1000);
            (filled_vec(la, 1000), filled_vec(lb, 1000))
        }
        7 => {
            // one element vs many
            let v = rng.gen_range_i32(0, 1000);
            let lb = rng.gen_range_usize(1, 1000);
            let b = make_vec(rng, lb, 0, 1000);
            (vec![v], b)
        }
        8 => {
            // many duplicates, few common values
            let la = rng.gen_range_usize(100, 1000);
            let lb = rng.gen_range_usize(100, 1000);
            let a = make_vec(rng, la, 0, 3);
            let b = make_vec(rng, lb, 2, 5);
            (a, b)
        }
        9 => {
            // A is subset multiset of B
            let la = rng.gen_range_usize(1, 500);
            let a = make_vec(rng, la, 0, 100);
            let mut b = a.clone();
            let extra = rng.gen_range_usize(0, 500);
            for _ in 0..extra {
                b.push(rng.gen_range_i32(0, 100));
            }
            (a, b)
        }
        _ => {
            // sorted ascending
            let la = rng.gen_range_usize(1, 200);
            let lb = rng.gen_range_usize(1, 200);
            let mut a = make_vec(rng, la, 0, 1000);
            let mut b = make_vec(rng, lb, 0, 1000);
            a.sort();
            b.sort();
            (a, b)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = make_case(&mut rng, mode);
        let (na, nb) = generate_test_case(a, b);
        print_json(&na, &nb);
    }
}