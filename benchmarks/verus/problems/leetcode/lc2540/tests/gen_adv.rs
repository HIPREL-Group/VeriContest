use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base1: Vec<i32>,
    base2: Vec<i32>,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= base1.len() <= 100_000,
        1 <= base2.len() <= 100_000,
        forall |i: int| 0 <= i < base1.len() ==> 1 <= #[trigger] base1[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < base2.len() ==> 1 <= #[trigger] base2[i] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i < j < base1.len() ==> base1[i] <= base1[j],
        forall |i: int, j: int| 0 <= i < j < base2.len() ==> base2[i] <= base2[j],
    ensures
        1 <= res.0.len() <= 100_000,
        1 <= res.1.len() <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i < j < res.0.len() ==> res.0[i] <= res.0[j],
        forall |i: int, j: int| 0 <= i < j < res.1.len() ==> res.1[i] <= res.1[j],
{
    (base1, base2)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn sorted_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v.sort();
    v
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // small disjoint
            let a = vec![1i32, 2, 3];
            let b = vec![4i32, 5, 6];
            (a, b)
        }
        1 => {
            // identical singletons
            let x = rng.gen_range_i32(1, 1_000_000_000);
            (vec![x], vec![x])
        }
        2 => {
            // example
            (vec![1, 2, 3], vec![2, 4])
        }
        3 => {
            // example2
            (vec![1, 2, 3, 6], vec![2, 3, 4, 5])
        }
        4 => {
            // disjoint singletons
            (vec![1], vec![2])
        }
        5 => {
            // large random
            let n1 = rng.gen_range_usize(50, 500);
            let n2 = rng.gen_range_usize(50, 500);
            let a = sorted_random(rng, n1, 1, 1000);
            let b = sorted_random(rng, n2, 1, 1000);
            (a, b)
        }
        6 => {
            // common at end
            let n = rng.gen_range_usize(5, 50);
            let mut a = sorted_random(rng, n, 1, 100);
            let mut b = sorted_random(rng, n, 101, 200);
            let v = 1_000_000_000i32;
            a.push(v);
            b.push(v);
            (a, b)
        }
        7 => {
            // boundary values
            (vec![1, 1_000_000_000], vec![1, 1_000_000_000])
        }
        8 => {
            // duplicates
            let n = rng.gen_range_usize(10, 100);
            let x = rng.gen_range_i32(1, 1000);
            let mut a = vec![x; n];
            let mut b = vec![x; n];
            a.sort();
            b.sort();
            (a, b)
        }
        9 => {
            // nums1 all small, nums2 all big (disjoint)
            let n1 = rng.gen_range_usize(5, 100);
            let n2 = rng.gen_range_usize(5, 100);
            let a = sorted_random(rng, n1, 1, 1000);
            let b = sorted_random(rng, n2, 1_000_001, 1_000_000_000);
            (a, b)
        }
        10 => {
            // large arrays
            let n = 1000usize;
            let a = sorted_random(rng, n, 1, 2000);
            let b = sorted_random(rng, n, 1, 2000);
            (a, b)
        }
        _ => {
            let n1 = rng.gen_range_usize(1, 50);
            let n2 = rng.gen_range_usize(1, 50);
            let a = sorted_random(rng, n1, 1, 50);
            let b = sorted_random(rng, n2, 1, 50);
            (a, b)
        }
    }
}

fn check_valid(v: &Vec<i32>) -> bool {
    if v.is_empty() || v.len() > 100_000 {
        return false;
    }
    for &x in v {
        if x < 1 || x > 1_000_000_000 {
            return false;
        }
    }
    for i in 1..v.len() {
        if v[i - 1] > v[i] {
            return false;
        }
    }
    true
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (a, b) = build_case(&mut rng, mode);
        if !check_valid(&a) || !check_valid(&b) {
            continue;
        }
        let (n1, n2) = generate_test_case(a, b);
        print_json(&n1, &n2);
    }
}