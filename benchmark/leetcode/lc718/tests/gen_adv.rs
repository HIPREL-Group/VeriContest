use vstd::prelude::*;

verus! {

pub fn generate_test_case(n1: usize, n2: usize, vals1: &Vec<i32>, vals2: &Vec<i32>) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= n1 <= 1000,
        1 <= n2 <= 1000,
        vals1.len() == n1,
        vals2.len() == n2,
        forall |i: int| 0 <= i < vals1.len() ==> 0 <= #[trigger] vals1[i] <= 100,
        forall |i: int| 0 <= i < vals2.len() ==> 0 <= #[trigger] vals2[i] <= 100,
    ensures
        1 <= res.0.len() <= 1000,
        1 <= res.1.len() <= 1000,
        (res.0.len() + 1) * (res.1.len() + 1) <= usize::MAX,
        forall |i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 100,
        forall |i: int| 0 <= i < res.1.len() ==> 0 <= #[trigger] res.1[i] <= 100,
{
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n1
        invariant
            n1 == vals1.len(),
            0 <= i <= n1,
            a.len() == i,
            forall |k: int| 0 <= k < a.len() ==> #[trigger] a[k] == vals1[k],
            forall |k: int| 0 <= k < vals1.len() ==> 0 <= #[trigger] vals1[k] <= 100,
        decreases n1 - i,
    {
        a.push(vals1[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n2
        invariant
            n2 == vals2.len(),
            0 <= j <= n2,
            b.len() == j,
            forall |k: int| 0 <= k < b.len() ==> #[trigger] b[k] == vals2[k],
            forall |k: int| 0 <= k < vals2.len() ==> 0 <= #[trigger] vals2[k] <= 100,
        decreases n2 - j,
    {
        b.push(vals2[j]);
        j = j + 1;
    }

    proof {
        assert(a.len() == n1);
        assert(b.len() == n2);
        assert(a.len() + 1 <= 1001);
        assert(b.len() + 1 <= 1001);
        assert((a.len() + 1) * (b.len() + 1) <= 1001 * 1001) by (nonlinear_arith)
            requires a.len() + 1 <= 1001, b.len() + 1 <= 1001;
        assert(1001 * 1001 <= usize::MAX);
    }

    (a, b)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_vec(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32(lo, hi));
    }
    v
}

fn build_const(n: usize, val: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn build_cycle(n: usize, pattern: &[i32]) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        v.push(pattern[i % pattern.len()]);
    }
    v
}

fn print_json(a: &[i32], b: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    print!("],\"nums2\":[");
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

    let total = 200usize;
    for t in 0..total {
        let mode = t % 12;
        let (a, b) = match mode {
            0 => {
                // small random
                let n1 = rng.gen_usize(1, 10);
                let n2 = rng.gen_usize(1, 10);
                let v1 = build_vec(&mut rng, n1, 0, 5);
                let v2 = build_vec(&mut rng, n2, 0, 5);
                generate_test_case(n1, n2, &v1, &v2)
            }
            1 => {
                // both length 1
                let v1 = build_vec(&mut rng, 1, 0, 100);
                let v2 = build_vec(&mut rng, 1, 0, 100);
                generate_test_case(1, 1, &v1, &v2)
            }
            2 => {
                // both max length, all zeros
                let v1 = build_const(1000, 0);
                let v2 = build_const(1000, 0);
                generate_test_case(1000, 1000, &v1, &v2)
            }
            3 => {
                // both max length, all same nonzero
                let v1 = build_const(1000, 100);
                let v2 = build_const(1000, 100);
                generate_test_case(1000, 1000, &v1, &v2)
            }
            4 => {
                // disjoint alphabets
                let n1 = rng.gen_usize(1, 500);
                let n2 = rng.gen_usize(1, 500);
                let v1 = build_vec(&mut rng, n1, 0, 49);
                let v2 = build_vec(&mut rng, n2, 50, 100);
                generate_test_case(n1, n2, &v1, &v2)
            }
            5 => {
                // example 1
                let v1 = vec![1,2,3,2,1];
                let v2 = vec![3,2,1,4,7];
                generate_test_case(5, 5, &v1, &v2)
            }
            6 => {
                // very different sizes
                let n1 = 1;
                let n2 = 1000;
                let v1 = build_vec(&mut rng, n1, 0, 100);
                let v2 = build_vec(&mut rng, n2, 0, 100);
                generate_test_case(n1, n2, &v1, &v2)
            }
            7 => {
                // alternating
                let n1 = rng.gen_usize(1, 1000);
                let n2 = rng.gen_usize(1, 1000);
                let v1 = build_cycle(n1, &[0, 1]);
                let v2 = build_cycle(n2, &[1, 0]);
                generate_test_case(n1, n2, &v1, &v2)
            }
            8 => {
                // repeated patterns
                let n1 = rng.gen_usize(1, 1000);
                let n2 = rng.gen_usize(1, 1000);
                let v1 = build_cycle(n1, &[1, 2, 3]);
                let v2 = build_cycle(n2, &[1, 2, 3]);
                generate_test_case(n1, n2, &v1, &v2)
            }
            9 => {
                // long common prefix
                let n = rng.gen_usize(10, 1000);
                let v1 = build_const(n, 7);
                let mut v2 = build_const(n, 7);
                // change tail of v2
                let last = v2.len() - 1;
                v2[last] = 8;
                generate_test_case(n, n, &v1, &v2)
            }
            10 => {
                // random wide range
                let n1 = rng.gen_usize(1, 1000);
                let n2 = rng.gen_usize(1, 1000);
                let v1 = build_vec(&mut rng, n1, 0, 100);
                let v2 = build_vec(&mut rng, n2, 0, 100);
                generate_test_case(n1, n2, &v1, &v2)
            }
            _ => {
                // small alphabet stress
                let n1 = rng.gen_usize(1, 1000);
                let n2 = rng.gen_usize(1, 1000);
                let v1 = build_vec(&mut rng, n1, 0, 2);
                let v2 = build_vec(&mut rng, n2, 0, 2);
                generate_test_case(n1, n2, &v1, &v2)
            }
        };
        print_json(&a, &b);
    }
}