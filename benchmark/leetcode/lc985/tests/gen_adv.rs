use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    vals: &Vec<i32>,
    idxs: &Vec<usize>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= nums_in.len() <= 10_000,
        forall|i: int| 0 <= i < nums_in.len() ==> -10_000 <= #[trigger] nums_in[i] <= 10_000,
        1 <= vals.len() <= 10_000,
        vals.len() == idxs.len(),
        forall|i: int| 0 <= i < vals.len() ==> -10_000 <= #[trigger] vals[i] <= 10_000,
        forall|i: int| 0 <= i < idxs.len() ==> #[trigger] idxs[i] < nums_in.len(),
    ensures
        ({
            let nums = result.0;
            let queries = result.1;
            &&& 1 <= nums.len() <= 10_000
            &&& (forall|i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000)
            &&& 1 <= queries.len() <= 10_000
            &&& (forall|i: int| 0 <= i < queries.len() ==>
                    queries[i].len() == 2
                    && -10_000 <= queries[i][0] <= 10_000
                    && 0 <= queries[i][1] < nums.len())
        }),
{
    // Build nums by cloning
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_in.len()
        invariant
            0 <= i <= nums_in.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums[k] == nums_in[k],
            forall|k: int| 0 <= k < nums_in.len() ==> -10_000 <= #[trigger] nums_in[k] <= 10_000,
        decreases nums_in.len() - i,
    {
        nums.push(nums_in[i]);
        i = i + 1;
    }

    let n = nums.len();

    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < vals.len()
        invariant
            0 <= j <= vals.len(),
            vals.len() == idxs.len(),
            queries.len() == j,
            n == nums.len(),
            n == nums_in.len(),
            1 <= n <= 10_000,
            forall|i: int| 0 <= i < vals.len() ==> -10_000 <= #[trigger] vals[i] <= 10_000,
            forall|i: int| 0 <= i < idxs.len() ==> #[trigger] idxs[i] < nums_in.len(),
            forall|k: int| 0 <= k < j as int ==> (#[trigger] queries[k]).len() == 2
                && -10_000 <= queries[k][0] <= 10_000
                && 0 <= queries[k][1] < n as int,
        decreases vals.len() - j,
    {
        let v = vals[j];
        let idx_i32: i32 = idxs[j] as i32;
        let mut q: Vec<i32> = Vec::new();
        q.push(v);
        q.push(idx_i32);
        assert(q.len() == 2);
        assert(q[0] == v);
        assert(q[1] == idx_i32);
        assert(idxs[j as int] < nums_in.len());
        assert(idx_i32 as int == idxs[j as int] as int);
        queries.push(q);
        assert(queries[j as int].len() == 2);
        j = j + 1;
    }

    (nums, queries)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn gen_nums_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { v.push(rng.gen_i32(-10_000, 10_000)); } }
        1 => { for _ in 0..n { v.push(0); } }
        2 => { for _ in 0..n { v.push(rng.gen_i32(-10_000, 10_000) * 2); } } // all even
        3 => { for _ in 0..n { v.push(rng.gen_i32(-5_000, 5_000) * 2 + 1); } } // all odd
        4 => { for _ in 0..n { v.push(10_000); } }
        5 => { for _ in 0..n { v.push(-10_000); } }
        6 => { for i in 0..n { v.push(if i % 2 == 0 { 10_000 } else { -10_000 }); } }
        7 => { for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 2 }); } }
        8 => { for _ in 0..n { v.push(rng.gen_i32(-3, 3)); } }
        9 => { for _ in 0..n { v.push(rng.gen_i32(-10_000, 10_000)); } }
        _ => { for _ in 0..n { v.push(rng.gen_i32(-10_000, 10_000)); } }
    }
    v
}

fn gen_queries_mode(rng: &mut Rng, mode: usize, q: usize, n: usize) -> (Vec<i32>, Vec<usize>) {
    let mut vals = Vec::with_capacity(q);
    let mut idxs = Vec::with_capacity(q);
    for i in 0..q {
        let val = match mode {
            0 => rng.gen_i32(-10_000, 10_000),
            1 => 1,
            2 => -1,
            3 => 10_000,
            4 => -10_000,
            5 => 0,
            6 => if i % 2 == 0 { 1 } else { -1 },
            7 => rng.gen_i32(-2, 2),
            8 => if rng.next_u64() % 2 == 0 { 10_000 } else { -10_000 },
            _ => rng.gen_i32(-10_000, 10_000),
        };
        let idx = match mode {
            0 => rng.gen_usize(0, n - 1),
            1 => 0,
            2 => n - 1,
            3 => i % n,
            _ => rng.gen_usize(0, n - 1),
        };
        vals.push(val);
        idxs.push(idx);
    }
    (vals, idxs)
}

fn print_json(nums: &[i32], queries: &[Vec<i32>]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"queries\":[");
    for i in 0..queries.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..queries[i].len() {
            if j > 0 { print!(","); }
            print!("{}", queries[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let nmode = t % 10;
        let qmode = (t / 10) % 9;

        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_usize(3, 20),
            3 => rng.gen_usize(20, 200),
            4 => rng.gen_usize(200, 2000),
            5 => 10_000,
            _ => rng.gen_usize(1, 500),
        };

        let q = match (t / 2) % 6 {
            0 => 1,
            1 => rng.gen_usize(1, 20),
            2 => rng.gen_usize(20, 500),
            3 => 10_000,
            4 => rng.gen_usize(500, 3000),
            _ => rng.gen_usize(1, 1000),
        };

        let nums = gen_nums_mode(&mut rng, nmode, n);
        let (vals, idxs) = gen_queries_mode(&mut rng, qmode, q, n);

        let (out_nums, out_queries) = generate_test_case(&nums, &vals, &idxs);
        print_json(&out_nums, &out_queries);
    }
}