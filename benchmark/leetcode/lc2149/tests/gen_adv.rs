use vstd::prelude::*;

verus! {

pub open spec fn filter_positive(s: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else if s[n - 1] > 0 {
        filter_positive(s, n - 1).push(s[n - 1])
    } else {
        filter_positive(s, n - 1)
    }
}

pub proof fn lemma_filter_positive_alt(s: Seq<i32>, t: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
        n <= t.len(),
        forall |i: int| 0 <= i < n ==> s[i] == t[i],
    ensures
        filter_positive(s, n) == filter_positive(t, n),
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_filter_positive_alt(s, t, n - 1);
    }
}

pub proof fn lemma_filter_positive_len(s: Seq<i32>, n: int)
    requires
        0 <= n,
        forall |i: int| 0 <= i < n ==> s[i] > 0,
    ensures
        filter_positive(s, n).len() == n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_filter_positive_len(s, n - 1);
    }
}

pub proof fn lemma_filter_positive_extend(s: Seq<i32>, n: int, k: int)
    requires
        0 <= n <= k <= s.len(),
        forall |i: int| n <= i < k ==> s[i] < 0,
    ensures
        filter_positive(s, k) == filter_positive(s, n),
    decreases k,
{
    if k <= n {
    } else {
        lemma_filter_positive_extend(s, n, k - 1);
    }
}

pub fn generate_test_case(
    n_half: usize,
    pos_vals: &Vec<i32>,
    neg_vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= n_half <= 100_000,
        pos_vals.len() == n_half,
        neg_vals.len() == n_half,
        forall |i: int| 0 <= i < n_half ==> 1 <= #[trigger] pos_vals[i] <= 100_000,
        forall |i: int| 0 <= i < n_half ==> -100_000 <= #[trigger] neg_vals[i] <= -1,
    ensures
        nums.len() == 2 * n_half,
        2 <= nums.len() <= 200_000,
        nums.len() % 2 == 0,
        forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] != 0,
        forall |i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
        filter_positive(nums@, nums.len() as int).len() == nums.len() as int / 2,
{
    let total: usize = 2 * n_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n_half
        invariant
            0 <= i <= n_half,
            nums.len() == i,
            pos_vals.len() == n_half,
            forall |k: int| 0 <= k < n_half ==> 1 <= #[trigger] pos_vals[k] <= 100_000,
            forall |k: int| 0 <= k < i ==> nums[k] == pos_vals[k],
            forall |k: int| 0 <= k < i ==> nums[k] > 0,
            forall |k: int| 0 <= k < i ==> 1 <= #[trigger] nums[k] <= 100_000,
        decreases n_half - i,
    {
        nums.push(pos_vals[i]);
        i = i + 1;
    }

    // Now nums has all positives. Add negatives.
    let mut j: usize = 0;
    while j < n_half
        invariant
            0 <= j <= n_half,
            nums.len() == n_half + j,
            neg_vals.len() == n_half,
            forall |k: int| 0 <= k < n_half ==> -100_000 <= #[trigger] neg_vals[k] <= -1,
            forall |k: int| 0 <= k < n_half ==> 1 <= #[trigger] nums[k] <= 100_000,
            forall |k: int| 0 <= k < n_half ==> nums[k] > 0,
            forall |k: int| n_half <= k < n_half + j ==> nums[k] == neg_vals[k - n_half],
            forall |k: int| n_half <= k < n_half + j ==> nums[k] < 0,
            forall |k: int| n_half <= k < n_half + j ==> -100_000 <= #[trigger] nums[k] <= -1,
        decreases n_half - j,
    {
        nums.push(neg_vals[j]);
        j = j + 1;
    }

    proof {
        assert(nums.len() == total);
        assert(total == 2 * n_half);
        assert(total % 2 == 0);

        assert forall |k: int| 0 <= k < nums.len() implies #[trigger] nums[k] != 0 by {
            if k < n_half as int {
                assert(nums[k] > 0);
            } else {
                assert(nums[k] < 0);
            }
        }

        assert forall |k: int| 0 <= k < nums.len() implies -100_000 <= #[trigger] nums[k] <= 100_000 by {
            if k < n_half as int {
                assert(1 <= nums[k] <= 100_000);
            } else {
                assert(-100_000 <= nums[k] <= -1);
            }
        }

        // Prove filter_positive length == n_half
        // First, filter_positive(nums@, n_half) == n_half since all are positive
        lemma_filter_positive_len(nums@, n_half as int);
        assert(filter_positive(nums@, n_half as int).len() == n_half as int);

        // Then extending from n_half to total adds only negatives
        lemma_filter_positive_extend(nums@, n_half as int, total as int);
        assert(filter_positive(nums@, total as int) == filter_positive(nums@, n_half as int));
        assert(filter_positive(nums@, nums.len() as int).len() == n_half as int);
        assert(nums.len() as int / 2 == n_half as int);
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_pos(&mut self) -> i32 {
        self.gen_range_usize(1, 100_000) as i32
    }
    fn gen_neg(&mut self) -> i32 {
        -(self.gen_range_usize(1, 100_000) as i32)
    }
}

fn emit(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn build_and_emit(n_half: usize, pos: Vec<i32>, neg: Vec<i32>) {
    let nums = generate_test_case(n_half, &pos, &neg);
    emit(&nums);
}

fn mode_random(rng: &mut Rng, n_half: usize) {
    let mut pos = Vec::with_capacity(n_half);
    let mut neg = Vec::with_capacity(n_half);
    for _ in 0..n_half { pos.push(rng.gen_pos()); }
    for _ in 0..n_half { neg.push(rng.gen_neg()); }
    build_and_emit(n_half, pos, neg);
}

fn mode_all_ones(n_half: usize) {
    let pos = vec![1i32; n_half];
    let neg = vec![-1i32; n_half];
    build_and_emit(n_half, pos, neg);
}

fn mode_max_vals(n_half: usize) {
    let pos = vec![100_000i32; n_half];
    let neg = vec![-100_000i32; n_half];
    build_and_emit(n_half, pos, neg);
}

fn mode_increasing(n_half: usize) {
    let mut pos = Vec::with_capacity(n_half);
    let mut neg = Vec::with_capacity(n_half);
    for i in 0..n_half {
        let v = ((i % 100_000) + 1) as i32;
        pos.push(v);
        neg.push(-v);
    }
    build_and_emit(n_half, pos, neg);
}

fn mode_decreasing(n_half: usize) {
    let mut pos = Vec::with_capacity(n_half);
    let mut neg = Vec::with_capacity(n_half);
    for i in 0..n_half {
        let v = (100_000 - (i % 100_000)) as i32;
        let v = if v < 1 { 1 } else { v };
        pos.push(v);
        neg.push(-v);
    }
    build_and_emit(n_half, pos, neg);
}

fn mode_mirror(n_half: usize) {
    // same values on both sides
    let mut pos = Vec::with_capacity(n_half);
    let mut neg = Vec::with_capacity(n_half);
    for i in 0..n_half {
        let v = ((i * 7 + 3) % 100_000 + 1) as i32;
        pos.push(v);
        neg.push(-v);
    }
    build_and_emit(n_half, pos, neg);
}

fn mode_alternating_sizes(rng: &mut Rng, n_half: usize) {
    let mut pos = Vec::with_capacity(n_half);
    let mut neg = Vec::with_capacity(n_half);
    for i in 0..n_half {
        if i % 2 == 0 {
            pos.push(1);
            neg.push(-100_000);
        } else {
            pos.push(100_000);
            neg.push(-1);
        }
        let _ = rng;
    }
    build_and_emit(n_half, pos, neg);
}

fn mode_small(rng: &mut Rng) {
    mode_random(rng, 1);
}

fn mode_large(rng: &mut Rng) {
    mode_random(rng, 100_000);
}

fn mode_medium(rng: &mut Rng, size: usize) {
    mode_random(rng, size);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        match mode {
            0 => mode_small(&mut rng),
            1 => mode_all_ones(1 + (t % 50)),
            2 => mode_max_vals(1 + (t % 100)),
            3 => mode_increasing(2 + (t % 200)),
            4 => mode_decreasing(2 + (t % 200)),
            5 => mode_mirror(5 + (t % 100)),
            6 => mode_alternating_sizes(&mut rng, 3 + (t % 80)),
            7 => mode_medium(&mut rng, 10 + (t % 500)),
            8 => {
                if t == 8 { mode_large(&mut rng); }
                else { mode_medium(&mut rng, 100 + (t % 300)); }
            }
            _ => mode_random(&mut rng, 2 + (t % 50)),
        }
    }
}