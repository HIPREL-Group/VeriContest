use vstd::prelude::*;

verus! {

pub open spec fn seq_bounded(s: Seq<i32>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> lo <= #[trigger] s[i] <= hi
}

pub open spec fn positive_diff_sum_spec(s: Seq<int>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        0
    } else {
        positive_diff_sum_spec(s, end - 1)
            + if s[end - 1] > s[end - 2] { s[end - 1] - s[end - 2] } else { 0int }
    }
}

pub open spec fn target_to_ints(target: Seq<i32>) -> Seq<int> {
    Seq::new(target.len(), |i: int| target[i] as int)
}

pub open spec fn algo_bound_spec(s: Seq<i32>) -> int {
    let ints = target_to_ints(s);
    ints[0] + positive_diff_sum_spec(ints, ints.len() as int)
}

// Lemma: if all elements are in [1, max_v], then positive_diff_sum <= (n-1)*max_v
pub proof fn lemma_pds_bound(s: Seq<int>, end: int, max_v: int)
    requires
        max_v >= 1,
        0 <= end <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= max_v,
    ensures
        0 <= positive_diff_sum_spec(s, end) <= (if end <= 1 { 0int } else { (end - 1) * max_v }),
    decreases end,
{
    if end <= 1 {
    } else {
        lemma_pds_bound(s, end - 1, max_v);
        assert(1 <= s[end - 1] <= max_v);
        assert(1 <= s[end - 2] <= max_v);
        if s[end - 1] > s[end - 2] {
            assert(s[end - 1] - s[end - 2] <= max_v - 1);
            assert(s[end - 1] - s[end - 2] <= max_v);
        }
        // (end-2)*max_v + max_v = (end-1)*max_v
        assert((end - 2) * max_v + max_v == (end - 1) * max_v) by (nonlinear_arith);
    }
}

pub fn generate_test_case(n: usize, filler: i32, special_idx: usize, special_val: i32) -> (target: Vec<i32>)
    requires
        1 <= n <= 100_000,
        1 <= filler <= 100,
        1 <= special_val <= 100,
        special_idx < n,
    ensures
        1 <= target.len() <= 100_000,
        target.len() == n,
        forall|i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 100,
        algo_bound_spec(target@) <= i32::MAX as int,
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            1 <= filler <= 100,
            1 <= special_val <= 100,
            special_idx < n,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] v[k] <= 100,
        decreases n - i,
    {
        if i == special_idx {
            v.push(special_val);
        } else {
            v.push(filler);
        }
        i = i + 1;
    }

    proof {
        let ints = target_to_ints(v@);
        assert(ints.len() == n as int);
        assert forall|k: int| 0 <= k < ints.len() implies 1 <= #[trigger] ints[k] <= 100 by {
            assert(ints[k] == v@[k] as int);
            assert(1 <= v@[k] <= 100);
        }
        lemma_pds_bound(ints, ints.len() as int, 100);
        // pds <= (n-1) * 100 <= 100_000 * 100 = 10_000_000
        // ints[0] <= 100
        // total <= 100 + 10_000_000 < i32::MAX (2_147_483_647)
        assert(n <= 100_000);
        assert((n as int - 1) * 100 <= 100_000 * 100) by (nonlinear_arith) requires n as int <= 100_000;
        assert(ints[0] <= 100);
        assert(algo_bound_spec(v@) <= 100 + 100_000 * 100);
    }

    v
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn print_case(target: &[i32]) {
    print!("{{\"target\":[");
    for i in 0..target.len() {
        if i > 0 { print!(","); }
        print!("{}", target[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => rng.range_usize(1, 10),
            3 => rng.range_usize(50, 200),
            4 => rng.range_usize(1000, 5000),
            5 => 100_000,
            6 => rng.range_usize(1, 100_000),
            7 => rng.range_usize(10, 100),
            8 => rng.range_usize(2, 20),
            _ => rng.range_usize(1, 1000),
        };

        let filler: i32 = match mode {
            0 => rng.range_i32(1, 100),
            1 => 1,
            2 => 100,
            3 => rng.range_i32(1, 10),
            4 => rng.range_i32(50, 100),
            5 => 1,
            6 => rng.range_i32(1, 100),
            7 => rng.range_i32(1, 100),
            8 => rng.range_i32(1, 5),
            _ => rng.range_i32(1, 100),
        };

        let special_idx: usize = if n == 0 { 0 } else { rng.range_usize(0, n - 1) };
        let special_val: i32 = match mode {
            2 => 1,
            3 => 100,
            4 => rng.range_i32(1, 100),
            5 => 100,
            6 => 100,
            7 => 1,
            8 => 100,
            _ => rng.range_i32(1, 100),
        };

        let v = generate_test_case(n, filler, special_idx, special_val);
        print_case(&v);
    }
}