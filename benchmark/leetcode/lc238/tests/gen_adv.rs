use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn product_of_range(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            1
        } else {
            nums[start] as int * Self::product_of_range(nums, start + 1, end)
        }
    }
}

// Strategy: generate an all-zero vector. Then every product range of length >= 1
// that includes any element is 0. The only nonzero products are empty ranges (=1).
// For i in [0, n): product_of_range(s, 0, i) * product_of_range(s, i+1, n)
//   - if i == 0: product(0,0)=1, product(1,n) = 0 (if n>1). = 0
//   - if i == n-1: product(0,n-1) = 0 (if n-1>=1). product(n,n)=1. = 0
//   - else: both 0. = 0
// All within i32 range.

pub proof fn lemma_product_all_zeros_is_zero_if_nonempty(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        start < end,
        forall|k: int| 0 <= k < s.len() ==> s[k] == 0i32,
    ensures
        Solution::product_of_range(s, start, end) == 0,
    decreases end - start
{
    if start + 1 >= end {
        // product = s[start] * product(start+1, end) = 0 * 1 = 0
        assert(Solution::product_of_range(s, start + 1, end) == 1);
        assert(s[start] == 0i32);
    } else {
        lemma_product_all_zeros_is_zero_if_nonempty(s, start + 1, end);
        assert(s[start] == 0i32);
    }
}

pub proof fn lemma_product_all_zeros(s: Seq<i32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|k: int| 0 <= k < s.len() ==> s[k] == 0i32,
    ensures
        Solution::product_of_range(s, start, end) == (if start >= end { 1int } else { 0int }),
{
    if start >= end {
        assert(Solution::product_of_range(s, start, end) == 1);
    } else {
        lemma_product_all_zeros_is_zero_if_nonempty(s, start, end);
    }
}

pub fn generate_test_case(n: usize) -> (nums: Vec<i32>)
    requires
        2 <= n <= 100_000,
    ensures
        nums.len() == n,
        2 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> -30 <= #[trigger] nums[i] <= 30,
        forall |i: int| 0 <= i < nums.len() ==>
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, 0, i) *
            Solution::product_of_range(nums@, i + 1, nums@.len() as int) <= i32::MAX,
        forall |i: int| 0 <= i <= nums.len() ==>
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, 0, i) <= i32::MAX,
        forall |i: int| 0 <= i <= nums.len() ==>
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, i, nums@.len() as int) <= i32::MAX,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            nums.len() == idx,
            idx <= n,
            forall|k: int| 0 <= k < nums.len() ==> nums[k] == 0i32,
        decreases n - idx
    {
        nums.push(0i32);
        idx = idx + 1;
    }

    proof {
        assert(nums.len() == n);
        assert(forall|k: int| 0 <= k < nums@.len() ==> nums@[k] == 0i32);

        assert forall|i: int| 0 <= i <= nums.len() implies
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, 0, i) <= i32::MAX
        by {
            lemma_product_all_zeros(nums@, 0, i);
        }

        assert forall|i: int| 0 <= i <= nums.len() implies
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, i, nums@.len() as int) <= i32::MAX
        by {
            lemma_product_all_zeros(nums@, i, nums@.len() as int);
        }

        assert forall|i: int| 0 <= i < nums.len() implies
            i32::MIN <= #[trigger] Solution::product_of_range(nums@, 0, i) *
            Solution::product_of_range(nums@, i + 1, nums@.len() as int) <= i32::MAX
        by {
            lemma_product_all_zeros(nums@, 0, i);
            lemma_product_all_zeros(nums@, i + 1, nums@.len() as int);
            let p = Solution::product_of_range(nums@, 0, i);
            let s = Solution::product_of_range(nums@, i + 1, nums@.len() as int);
            // p in {0,1}, s in {0,1}, so p*s in {0,1}
            assert(p == 0 || p == 1);
            assert(s == 0 || s == 1);
        }
    }

    nums
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
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
        let n: usize = match mode {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 10000,
            7 => 100000,
            8 => rng.gen_range_usize(2, 1000),
            _ => rng.gen_range_usize(2, 100000),
        };
        let nums = generate_test_case(n);
        print_json(&nums);
    }
}