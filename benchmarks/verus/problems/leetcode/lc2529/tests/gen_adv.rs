use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> -2000 <= #[trigger] result[i] <= 2000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 2000 { 2000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 2000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -2000 <= #[trigger] result[j] <= 2000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] <= result[k],
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let mut value = if value < -2000 { -2000 } else if value > 2000 { 2000 } else { value };
        if i > 0 && value < result[i - 1] { value = result[i - 1]; }
        assert forall|j: int| 0 <= j < result.len() implies result[j] <= value by {
            if j < i - 1 { assert(result[j] <= result[(i - 1) as int]); }
        }
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 2000,
        forall |i: int| 0 <= i < values.len() ==> -2000 <= #[trigger] values[i] <= 2000,
    ensures
        1 <= nums.len() <= 2000,
        forall |i: int| 0 <= i < nums.len() ==> -2000 <= #[trigger] nums[i] <= 2000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 2000,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -2000 <= #[trigger] values[k] <= 2000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -2000 <= #[trigger] nums[k] <= 2000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    nums
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_sorted_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-2000, 2000)).collect();
    v.sort();
    v
}

fn make_all_negative(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    v.sort();
    v
}

fn make_all_positive(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 2000)).collect();
    v.sort();
    v
}

fn make_all_zero(n: usize) -> Vec<i32> {
    vec![0; n]
}

fn make_with_zeros(rng: &mut Rng, n: usize) -> Vec<i32> {
    let neg_count = rng.gen_range_usize(0, n);
    let zero_count = if n > neg_count { rng.gen_range_usize(0, n - neg_count) } else { 0 };
    let pos_count = n - neg_count - zero_count;
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let mut negs: Vec<i32> = (0..neg_count).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    negs.sort();
    for x in negs { v.push(x); }
    for _ in 0..zero_count { v.push(0); }
    let mut poss: Vec<i32> = (0..pos_count).map(|_| rng.gen_range_i32(1, 2000)).collect();
    poss.sort();
    for x in poss { v.push(x); }
    v
}

fn make_balanced(rng: &mut Rng, n: usize) -> Vec<i32> {
    let k = n / 2;
    let mut negs: Vec<i32> = (0..k).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    negs.sort();
    let mut poss: Vec<i32> = (0..(n - k)).map(|_| rng.gen_range_i32(1, 2000)).collect();
    poss.sort();
    let mut v = Vec::new();
    for x in negs { v.push(x); }
    for x in poss { v.push(x); }
    v
}

fn make_more_neg(rng: &mut Rng, n: usize) -> Vec<i32> {
    let k = (n * 3) / 4;
    let mut negs: Vec<i32> = (0..k).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    negs.sort();
    let mut poss: Vec<i32> = (0..(n - k)).map(|_| rng.gen_range_i32(1, 2000)).collect();
    poss.sort();
    let mut v = Vec::new();
    for x in negs { v.push(x); }
    for x in poss { v.push(x); }
    v
}

fn make_more_pos(rng: &mut Rng, n: usize) -> Vec<i32> {
    let k = n / 4;
    let mut negs: Vec<i32> = (0..k).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    negs.sort();
    let mut poss: Vec<i32> = (0..(n - k)).map(|_| rng.gen_range_i32(1, 2000)).collect();
    poss.sort();
    let mut v = Vec::new();
    for x in negs { v.push(x); }
    for x in poss { v.push(x); }
    v
}

fn make_single(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(-2000, 2000)]
}

fn make_many_zeros(rng: &mut Rng, n: usize) -> Vec<i32> {
    let neg = n / 3;
    let pos = n / 3;
    let zero = n - neg - pos;
    let mut negs: Vec<i32> = (0..neg).map(|_| rng.gen_range_i32(-2000, -1)).collect();
    negs.sort();
    let mut poss: Vec<i32> = (0..pos).map(|_| rng.gen_range_i32(1, 2000)).collect();
    poss.sort();
    let mut v = Vec::new();
    for x in negs { v.push(x); }
    for _ in 0..zero { v.push(0); }
    for x in poss { v.push(x); }
    v
}

fn make_extremes(n: usize) -> Vec<i32> {
    let k = n / 2;
    let mut v = Vec::new();
    for _ in 0..k { v.push(-2000); }
    for _ in 0..(n - k) { v.push(2000); }
    v
}

fn print_json(nums: &[i32]) {
        let nums = generate_test_case(nums.to_vec());
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            0 => 1,
            1 => 2000,
            2 => rng.gen_range_usize(1, 10),
            3 => rng.gen_range_usize(100, 500),
            4 => 2000,
            _ => rng.gen_range_usize(1, 2000),
        };

        let values: Vec<i32> = match mode {
            0 => make_single(&mut rng),
            1 => make_all_zero(n),
            2 => make_all_negative(&mut rng, n),
            3 => make_all_positive(&mut rng, n),
            4 => make_balanced(&mut rng, n),
            5 => make_more_neg(&mut rng, n),
            6 => make_more_pos(&mut rng, n),
            7 => make_with_zeros(&mut rng, n),
            8 => make_many_zeros(&mut rng, n),
            9 => make_extremes(n),
            _ => make_sorted_random(&mut rng, n),
        };

        let nums = generate_candidate(&values);
        print_json(&nums);
    }
}
