use vstd::prelude::*;

verus! {

pub open spec fn total_len(nums: Seq<Seq<i32>>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 } else { total_len(nums, end - 1) + nums[end - 1].len() as int }
}
proof fn row_sum_append(rows: Seq<Seq<i32>>, row: Seq<i32>, end: int)
    requires 0 <= end <= rows.len(),
    ensures total_len(rows.push(row), end) == total_len(rows, end),
    decreases end,
{
    if end > 0 { row_sum_append(rows, row, end - 1); }
}
fn unique_row(raw: &Vec<i32>, budget: usize) -> (result: Vec<i32>)
    requires 1 <= budget <= 1000,
    ensures 1 <= result.len() <= budget,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > budget { budget } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= budget, 1 <= budget <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 1000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 1000 { 1000 } else { v };
        let mut found = false;
        let mut j = 0usize;
        while j < result.len()
            invariant j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    if result.len() == 0 { result.push(1); }
    result
}
pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures 1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() >= 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 1 <= #[trigger] result[i][j] <= 1000,
        1 <= total_len(result.deep_view(), result.len() as int) <= 1000,
        forall|i: int, j: int, k: int| 0 <= i < result.len() && 0 <= j < k < result[i].len() ==> result[i][j] != result[i][k],
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let empty: Vec<i32> = Vec::new();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut total = 0usize;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 1000, result.len() == i,
            i <= total <= 1000 - (n - i), total == total_len(result.deep_view(), i as int),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() >= 1,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < result[j].len() ==> 1 <= #[trigger] result[j][k] <= 1000,
            forall|j: int, k: int, l: int| 0 <= j < i && 0 <= k < l < result[j].len() ==> result[j][k] != result[j][l],
        decreases n - i,
    {
        let budget = 1000 - total - (n - i - 1);
        let row = unique_row(if i < raw.len() { &raw[i] } else { &empty }, budget);
        let ghost rows = result.deep_view();
        let ghost row_view = row.deep_view();
        total += row.len();
        result.push(row);
        proof {
            assert(result.deep_view() =~= rows.push(row_view));
            row_sum_append(rows, row_view, i as int);
        }
        i += 1;
    }
    result
}


pub fn generate_candidate(
    n: usize,
    vals: &Vec<i32>,
) -> (nums: Vec<Vec<i32>>)
    requires
        1 <= n <= 1000,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i].len() >= 1,
        forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums[i].len() ==> 1 <= #[trigger] nums[i][j] <= 1000,
{
    let mut nums: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            1 <= n <= 1000,
            vals.len() == n,
            nums.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] nums[k]).len() == 1,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] nums[k])[0] == vals[k],
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        row.push(vals[i]);
        assert(row.len() == 1);
        assert(row[0] == vals[i as int]);
        nums.push(row);
        i = i + 1;
    }

    proof {
        assert forall|a: int, b: int| 0 <= a < nums.len() && 0 <= b < nums[a].len() implies 1 <= #[trigger] nums[a][b] <= 1000 by {
            assert(nums[a].len() == 1);
            assert(b == 0);
            assert(nums[a][0] == vals[a]);
            assert(1 <= vals[a] <= 1000);
        }
    }

    nums
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_row(rng: &mut Rng, mode: usize, row_idx: usize, n_rows: usize) -> Vec<i32> {
    // Return distinct positive integers, each in [1,1000]. But generator takes only one value per row.
    // For diversity we pick the first element; extras won't be exposed to the generator since we call with single-element rows.
    let v = match mode {
        0 => rng.gen_range_i32(1, 1000),
        1 => 1,
        2 => 1000,
        3 => rng.gen_range_i32(1, 10),
        4 => 500,
        5 => if row_idx == 0 { 7 } else { rng.gen_range_i32(1, 1000) },
        6 => if row_idx == n_rows - 1 { 7 } else { rng.gen_range_i32(1, 1000) },
        7 => rng.gen_range_i32(1, 3),
        8 => rng.gen_range_i32(990, 1000),
        9 => (row_idx as i32 % 1000) + 1,
        _ => rng.gen_range_i32(1, 1000),
    };
    vec![v]
}

fn print_json(nums: &Vec<Vec<i32>>) {
    let nums = generate_test_case(nums.clone());
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..nums[i].len() {
            if j > 0 { print!(","); }
            print!("{}", nums[i][j]);
        }
        print!("]");
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 1000,
            2 => 1,
            3 => 2 + (t % 8),
            4 => 500,
            5 => 50,
            6 => 100,
            7 => 10,
            8 => 1000,
            9 => 300,
            _ => 1 + (t % 999),
        };
        let n = if n == 0 { 1 } else if n > 1000 { 1000 } else { n };

        let mut vals: Vec<i32> = Vec::with_capacity(n);
        for i in 0..n {
            let r = build_row(&mut rng, mode, i, n);
            vals.push(r[0]);
        }
        let nums = generate_candidate(n, &vals);
        print_json(&nums);
    }
}
