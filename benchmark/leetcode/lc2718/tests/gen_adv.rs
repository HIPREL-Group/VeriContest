use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    types: &Vec<i32>,
    indices: &Vec<i32>,
    vals: &Vec<i32>,
) -> (res: (i32, Vec<Vec<i32>>))
    requires
        1 <= n <= 10000,
        1 <= types.len() <= 50000,
        types.len() == indices.len(),
        types.len() == vals.len(),
        forall|i: int| 0 <= i < types.len() ==> (#[trigger] types[i] == 0 || types[i] == 1),
        forall|i: int| 0 <= i < indices.len() ==> 0 <= #[trigger] indices[i] && indices[i] < n,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] && vals[i] <= 100000,
    ensures
        ({
            let (rn, rq) = res;
            &&& 1 <= rn <= 10000
            &&& 1 <= rq.len() <= 50000
            &&& (forall|i: int| 0 <= i < rq.len() ==> (#[trigger] rq[i]).len() == 3)
            &&& (forall|i: int| 0 <= i < rq.len() ==> (#[trigger] rq[i][0] == 0 || rq[i][0] == 1))
            &&& (forall|i: int| 0 <= i < rq.len() ==> 0 <= #[trigger] rq[i][1] && rq[i][1] < rn)
            &&& (forall|i: int| 0 <= i < rq.len() ==> 0 <= #[trigger] rq[i][2] && rq[i][2] <= 100000)
        }),
{
    let m = types.len();
    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            m == types.len(),
            types.len() == indices.len(),
            types.len() == vals.len(),
            0 <= i <= m,
            queries.len() == i,
            1 <= n <= 10000,
            1 <= m <= 50000,
            forall|k: int| 0 <= k < types.len() ==> (#[trigger] types[k] == 0 || types[k] == 1),
            forall|k: int| 0 <= k < indices.len() ==> 0 <= #[trigger] indices[k] && indices[k] < n,
            forall|k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] && vals[k] <= 100000,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] queries[k]).len() == 3,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] queries[k][0] == 0 || queries[k][0] == 1),
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] queries[k][1] && queries[k][1] < n,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] queries[k][2] && queries[k][2] <= 100000,
        decreases m - i,
    {
        let mut q: Vec<i32> = Vec::new();
        q.push(types[i]);
        q.push(indices[i]);
        q.push(vals[i]);
        assert(q.len() == 3);
        assert(q[0] == types[i as int]);
        assert(q[1] == indices[i as int]);
        assert(q[2] == vals[i as int]);
        queries.push(q);
        i = i + 1;
    }

    (n, queries)
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

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_test(rng: &mut Rng, n: i32, m: usize, mode: usize) -> (i32, Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut types = Vec::with_capacity(m);
    let mut indices = Vec::with_capacity(m);
    let mut vals = Vec::with_capacity(m);

    for i in 0..m {
        let t = match mode {
            0 => rng.gen_i32(0, 1),
            1 => 0,
            2 => 1,
            3 => if i % 2 == 0 { 0 } else { 1 },
            4 => rng.gen_i32(0, 1),
            5 => rng.gen_i32(0, 1),
            6 => rng.gen_i32(0, 1),
            7 => rng.gen_i32(0, 1),
            8 => rng.gen_i32(0, 1),
            _ => rng.gen_i32(0, 1),
        };

        let idx = match mode {
            4 => 0, // always same index
            5 => rng.gen_i32(0, if n - 1 < 2 { n - 1 } else { 1 }), // limited indices
            6 => n - 1,
            7 => i as i32 % n,
            _ => rng.gen_i32(0, n - 1),
        };

        let v = match mode {
            8 => 0,
            9 => 100000,
            5 => rng.gen_i32(0, 10),
            _ => rng.gen_i32(0, 100000),
        };

        types.push(t);
        indices.push(idx);
        vals.push(v);
    }

    (n, types, indices, vals)
}

fn print_json(n: i32, queries: &[Vec<i32>]) {
    print!("{{\"n\":{},\"queries\":[", n);
    for i in 0..queries.len() {
        if i > 0 { print!(","); }
        print!("[{},{},{}]", queries[i][0], queries[i][1], queries[i][2]);
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
        let mode = t % 10;
        let n: i32 = match mode {
            0 => rng.gen_i32(1, 20),
            1 => rng.gen_i32(1, 100),
            2 => 1,
            3 => 10000,
            4 => rng.gen_i32(2, 50),
            5 => rng.gen_i32(10, 200),
            6 => 2,
            7 => rng.gen_i32(3, 10),
            8 => rng.gen_i32(100, 1000),
            _ => rng.gen_i32(1, 10000),
        };

        let m: usize = match mode {
            0 => rng.gen_usize(1, 20),
            1 => rng.gen_usize(1, 100),
            2 => rng.gen_usize(1, 50),
            3 => rng.gen_usize(1000, 5000),
            4 => rng.gen_usize(10, 100),
            5 => rng.gen_usize(50, 500),
            6 => rng.gen_usize(1, 50),
            7 => rng.gen_usize(5, 50),
            8 => 50000,
            _ => rng.gen_usize(1, 1000),
        };

        let (nn, types, indices, vals) = build_test(&mut rng, n, m, mode);
        let (rn, queries) = generate_test_case(nn, &types, &indices, &vals);
        print_json(rn, &queries);
    }
}