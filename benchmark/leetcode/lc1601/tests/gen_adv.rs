use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    raw: &Vec<(i32, i32)>,
) -> (result: (i32, Vec<Vec<i32>>))
    requires
        1 <= n <= 20,
        1 <= raw.len() <= 16,
        forall|i: int| 0 <= i < raw.len() ==>
            0 <= (#[trigger] raw[i]).0 < n && 0 <= raw[i].1 < n,
    ensures
        ({
            let (nn, requests) = result;
            &&& nn == n
            &&& 1 <= requests.len() <= 16
            &&& requests.len() == raw.len()
            &&& forall|i: int| 0 <= i < requests.len() ==>
                    #[trigger] requests[i].len() == 2
                    && 0 <= requests[i][0] < n
                    && 0 <= requests[i][1] < n
        }),
{
    let mut requests: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < raw.len()
        invariant
            0 <= i <= raw.len(),
            requests.len() == i,
            1 <= n <= 20,
            1 <= raw.len() <= 16,
            forall|k: int| 0 <= k < raw.len() ==>
                0 <= (#[trigger] raw[k]).0 < n && 0 <= raw[k].1 < n,
            forall|k: int| 0 <= k < i ==>
                #[trigger] requests[k].len() == 2
                && 0 <= requests[k][0] < n
                && 0 <= requests[k][1] < n,
        decreases raw.len() - i,
    {
        let (f, t) = raw[i];
        let mut pair: Vec<i32> = Vec::new();
        pair.push(f);
        pair.push(t);
        assert(pair.len() == 2);
        assert(pair[0] == f);
        assert(pair[1] == t);
        requests.push(pair);
        i = i + 1;
    }
    (n, requests)
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
        let span = (hi - lo + 1) as i64;
        lo + ((self.next_u64() as i64).rem_euclid(span)) as i32
    }
}

fn build_requests(mode: usize, rng: &mut Rng, t: usize) -> (i32, Vec<(i32, i32)>) {
    match mode {
        0 => {
            // minimal n=1, all self-loops
            let m = rng.gen_range_usize(1, 16);
            let mut v = Vec::new();
            for _ in 0..m {
                v.push((0i32, 0i32));
            }
            (1, v)
        }
        1 => {
            // n=2, simple swap pairs
            let m = rng.gen_range_usize(1, 16);
            let mut v = Vec::new();
            for i in 0..m {
                if i % 2 == 0 {
                    v.push((0i32, 1i32));
                } else {
                    v.push((1i32, 0i32));
                }
            }
            (2, v)
        }
        2 => {
            // all same from->to (unbalanced-friendly)
            let n = rng.gen_range_i32(2, 20);
            let m = rng.gen_range_usize(1, 16);
            let mut v = Vec::new();
            let a = rng.gen_range_i32(0, n - 1);
            let mut b = rng.gen_range_i32(0, n - 1);
            if b == a { b = (b + 1) % n; }
            for _ in 0..m {
                v.push((a, b));
            }
            (n, v)
        }
        3 => {
            // perfect cycle
            let n = rng.gen_range_i32(2, 16);
            let mut v = Vec::new();
            for i in 0..n {
                v.push((i, (i + 1) % n));
            }
            (n, v)
        }
        4 => {
            // example 1
            let v = vec![(0,1),(1,0),(0,1),(1,2),(2,0),(3,4)];
            (5, v)
        }
        5 => {
            // example 2
            let v = vec![(0,0),(1,2),(2,1)];
            (3, v)
        }
        6 => {
            // example 3
            let v = vec![(0,3),(3,1),(1,2),(2,0)];
            (4, v)
        }
        7 => {
            // max n, max m, random
            let m = 16usize;
            let n = 20i32;
            let mut v = Vec::new();
            for _ in 0..m {
                let a = rng.gen_range_i32(0, n - 1);
                let b = rng.gen_range_i32(0, n - 1);
                v.push((a, b));
            }
            (n, v)
        }
        8 => {
            // single request
            let n = rng.gen_range_i32(1, 20);
            let a = rng.gen_range_i32(0, n - 1);
            let b = rng.gen_range_i32(0, n - 1);
            (n, vec![(a, b)])
        }
        9 => {
            // all self-loops random n
            let n = rng.gen_range_i32(1, 20);
            let m = rng.gen_range_usize(1, 16);
            let mut v = Vec::new();
            for _ in 0..m {
                let a = rng.gen_range_i32(0, n - 1);
                v.push((a, a));
            }
            (n, v)
        }
        _ => {
            // fully random
            let n = rng.gen_range_i32(1, 20);
            let m = rng.gen_range_usize(1, 16);
            let mut v = Vec::new();
            for _ in 0..m {
                let a = rng.gen_range_i32(0, n - 1);
                let b = rng.gen_range_i32(0, n - 1);
                v.push((a, b));
            }
            let _ = t;
            (n, v)
        }
    }
}

fn print_json(n: i32, requests: &Vec<Vec<i32>>) {
    print!("{{\"n\":{},\"requests\":[", n);
    for i in 0..requests.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", requests[i][0], requests[i][1]);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, raw) = build_requests(mode, &mut rng, t);
        let (nn, requests) = generate_test_case(n, &raw);
        print_json(nn, &requests);
    }
}