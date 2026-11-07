use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    queries_in: &Vec<Vec<i32>>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= queries_in.len() <= nums_in.len() <= 100_000,
        forall |i: int| 0 <= i < nums_in.len() ==> 1 <= #[trigger] nums_in[i] <= 100_000,
        forall |i: int| 0 <= i < queries_in.len() ==> (#[trigger] queries_in[i]).len() == 2,
        forall |i: int| 0 <= i < queries_in.len() ==> 0 <= (#[trigger] queries_in[i])[0] < nums_in.len(),
        forall |i: int| 0 <= i < queries_in.len() ==> 0 <= (#[trigger] queries_in[i])[1] <= nums_in.len() - 1,
    ensures
        1 <= result.1.len() <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall |i: int| 0 <= i < result.1.len() && result.1[i].len() == 2 ==> 0 <= #[trigger] result.1[i][0] < result.0.len(),
        forall |i: int| 0 <= i < result.1.len() && result.1[i].len() == 2 ==> 0 <= #[trigger] result.1[i][1] <= result.0.len() - 1,
{
    let n = nums_in.len();
    let m = queries_in.len();

    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == nums_in.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == nums_in[k],
            forall |k: int| 0 <= k < nums_in.len() ==> 1 <= #[trigger] nums_in[k] <= 100_000,
        decreases n - i,
    {
        nums.push(nums_in[i]);
        i = i + 1;
    }

    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            n == nums_in.len(),
            m == queries_in.len(),
            nums.len() == n,
            0 <= j <= m,
            queries.len() == j,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
            forall |k: int| 0 <= k < queries_in.len() ==> (#[trigger] queries_in[k]).len() == 2,
            forall |k: int| 0 <= k < queries_in.len() ==> 0 <= (#[trigger] queries_in[k])[0] < nums_in.len(),
            forall |k: int| 0 <= k < queries_in.len() ==> 0 <= (#[trigger] queries_in[k])[1] <= nums_in.len() - 1,
            forall |k: int| 0 <= k < j as int ==> (#[trigger] queries[k]).len() == 2,
            forall |k: int| 0 <= k < j as int ==> 0 <= (#[trigger] queries[k])[0] < nums.len(),
            forall |k: int| 0 <= k < j as int ==> 0 <= (#[trigger] queries[k])[1] <= nums.len() - 1,
        decreases m - j,
    {
        assert(queries_in[j as int].len() == 2);
        assert(0 <= queries_in[j as int][0] < nums_in.len());
        assert(0 <= queries_in[j as int][1] <= nums_in.len() - 1);
        let q = &queries_in[j];
        let a = q[0];
        let b = q[1];
        let mut new_q: Vec<i32> = Vec::new();
        new_q.push(a);
        new_q.push(b);
        assert(new_q.len() == 2);
        assert(new_q[0] == a);
        assert(new_q[1] == b);
        queries.push(new_q);
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

fn build(n: usize, m: usize, nums_vals: Vec<i32>, queries_vals: Vec<(i32, i32)>) -> (Vec<i32>, Vec<Vec<i32>>) {
    assert!(nums_vals.len() == n);
    assert!(queries_vals.len() == m);
    let mut nums_in: Vec<i32> = Vec::with_capacity(n);
    for v in &nums_vals {
        let mut vv = *v;
        if vv < 1 { vv = 1; }
        if vv > 100_000 { vv = 100_000; }
        nums_in.push(vv);
    }
    let mut queries_in: Vec<Vec<i32>> = Vec::with_capacity(m);
    for (a, b) in &queries_vals {
        let mut aa = *a;
        let mut bb = *b;
        if aa < 0 { aa = 0; }
        if aa >= n as i32 { aa = n as i32 - 1; }
        if bb < 0 { bb = 0; }
        if bb > n as i32 - 1 { bb = n as i32 - 1; }
        let mut q = Vec::new();
        q.push(aa);
        q.push(bb);
        queries_in.push(q);
    }
    generate_test_case(&nums_in, &queries_in)
}

fn print_json(nums: &Vec<i32>, queries: &Vec<Vec<i32>>) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"queries\":[");
    for i in 0..queries.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", queries[i][0], queries[i][1]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize, idx: usize) -> (usize, usize, Vec<i32>, Vec<(i32, i32)>) {
    match mode {
        0 => {
            // minimal size
            let n = 1;
            let m = 1;
            let nums = vec![rng.gen_range_i32(1, 100_000)];
            let queries = vec![(0i32, 0i32)];
            (n, m, nums, queries)
        }
        1 => {
            // all equal values
            let n = rng.gen_range_usize(2, 50);
            let m = rng.gen_range_usize(1, n);
            let v = rng.gen_range_i32(1, 100_000);
            let nums: Vec<i32> = (0..n).map(|_| v).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        2 => {
            // strictly increasing
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|i| (i as i32 + 1)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        3 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|i| (n - i) as i32).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        4 => {
            // k = 0 always
            let n = rng.gen_range_usize(2, 80);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), 0i32)
            }).collect();
            (n, m, nums, queries)
        }
        5 => {
            // k = n - 1 (max)
            let n = rng.gen_range_usize(2, 80);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), n as i32 - 1)
            }).collect();
            (n, m, nums, queries)
        }
        6 => {
            // large n
            let n = rng.gen_range_usize(1000, 5000);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100_000)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        7 => {
            // duplicates ties (smallest indices matter)
            let n = rng.gen_range_usize(5, 100);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 3)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        8 => {
            // always same index queried
            let n = rng.gen_range_usize(3, 100);
            let m = rng.gen_range_usize(1, n);
            let idx0 = rng.gen_range_i32(0, n as i32 - 1);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (idx0, rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            (n, m, nums, queries)
        }
        9 => {
            // example from prompt
            let nums = vec![1, 2, 2, 1, 2, 3, 1];
            let queries = vec![(1i32, 2i32), (3i32, 3i32), (4i32, 2i32)];
            (7, 3, nums, queries)
        }
        _ => {
            // random general
            let n = rng.gen_range_usize(1, 200);
            let m = rng.gen_range_usize(1, n);
            let nums: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100_000)).collect();
            let queries: Vec<(i32, i32)> = (0..m).map(|_| {
                (rng.gen_range_i32(0, n as i32 - 1), rng.gen_range_i32(0, n as i32 - 1))
            }).collect();
            let _ = idx;
            (n, m, nums, queries)
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
        let (n, m, nums, queries) = gen_mode(&mut rng, mode, t);
        let (nums_out, queries_out) = build(n, m, nums, queries);
        print_json(&nums_out, &queries_out);
    }
}