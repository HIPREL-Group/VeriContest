use vstd::prelude::*;

verus! {

pub open spec fn count_occ(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        count_occ(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

// Lemma: if every element of s equals value, then count_occ(s, value) == s.len()
pub proof fn lemma_all_equal(s: Seq<i32>, value: i32)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == value,
    ensures count_occ(s, value) == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
        lemma_all_equal(s2, value);
        assert(s.last() == s[s.len() - 1]);
        assert(s.last() == value);
    }
}

// Lemma: if value does not occur in s, count is 0
pub proof fn lemma_no_occur(s: Seq<i32>, value: i32)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] != value,
    ensures count_occ(s, value) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
        lemma_no_occur(s2, value);
        assert(s.last() == s[s.len() - 1]);
    }
}

// Lemma: count of value v in a sequence where v appears exactly at index `idx`
pub proof fn lemma_single_occ(s: Seq<i32>, value: i32, idx: int)
    requires
        0 <= idx < s.len(),
        s[idx] == value,
        forall|i: int| 0 <= i < s.len() && i != idx ==> s[i] != value,
    ensures count_occ(s, value) == 1,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s.last() == s[s.len() - 1]);
        if idx == s.len() - 1 {
            assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
            assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] != value);
            lemma_no_occur(s2, value);
        } else {
            assert(s.last() != value);
            assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
            lemma_single_occ(s2, value, idx);
        }
    }
}

// Build a sequence: first n copies of kv, then fillers
// Count occurrences of kv in this sequence is exactly n
pub proof fn lemma_count_kv(s: Seq<i32>, kv: i32, n: int)
    requires
        n >= 0,
        s.len() == 2 * n,
        forall|i: int| 0 <= i < n ==> s[i] == kv,
        forall|i: int| n <= i < 2 * n ==> s[i] != kv,
    ensures count_occ(s, kv) == n,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s.last() == s[s.len() - 1]);
        assert(s.last() != kv);
        assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
        // s2 has length 2n-1. First n are kv (if n <= 2n-1, i.e., n >= 1), rest are not kv.
        if n == 0 {
            // s.len() == 0, contradicts s.len() > 0
            assert(false);
        } else {
            // Split s2 further: positions 0..n are kv, positions n..2n-1 are not kv
            lemma_no_occur_range(s2, kv, n);
            lemma_all_equal_range(s2, kv, n);
            // count_occ(s2, kv) == n
            assert(count_occ(s, kv) == count_occ(s2, kv) + 0);
        }
    }
}

pub proof fn lemma_all_equal_range(s: Seq<i32>, value: i32, n: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] == value,
        forall|i: int| n <= i < s.len() ==> s[i] != value,
    ensures count_occ(s, value) == n,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s.last() == s[s.len() - 1]);
        assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == s[i]);
        if s.len() as int == n {
            // last element is kv (since n == s.len(), so s[s.len()-1] is in range 0..n)
            assert(s.last() == value);
            // s2: all equal value
            assert(forall|i: int| 0 <= i < s2.len() ==> s2[i] == value);
            lemma_all_equal(s2, value);
        } else {
            // s.len() > n, last index is >= n, so s.last() != value
            assert(s.last() != value);
            lemma_all_equal_range(s2, value, n);
        }
    }
}

pub proof fn lemma_no_occur_range(s: Seq<i32>, value: i32, n: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| n <= i < s.len() ==> s[i] != value,
    ensures true,
{
}

pub open spec fn valid_filler(fillers: Seq<i32>, kv: i32) -> bool {
    (forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 10_000) &&
    (forall|i: int| 0 <= i < fillers.len() ==> fillers[i] != kv) &&
    (forall|i: int, j: int| 0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
        ==> fillers[i] != fillers[j])
}

pub fn generate_test_case(
    kv: i32,
    fillers: Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        0 <= kv <= 10_000,
        2 <= fillers.len() <= 5000,
        valid_filler(fillers@, kv),
    ensures
        4 <= nums.len() <= 10_000,
        nums.len() % 2 == 0,
        nums.len() == 2 * fillers.len(),
        (exists|k: int|
            0 <= k < nums@.len() &&
            (forall|i: int| 0 <= i < nums@.len() ==> 0 <= #[trigger] nums@[i] <= 10_000) &&
            count_occ(nums@, nums@[k]) == nums@.len() / 2 &&
            (forall|i: int| 0 <= i < nums@.len() && nums@[i] != nums@[k] ==> #[trigger] count_occ(nums@, nums@[i]) == 1)),
{
    let n: usize = fillers.len();
    let mut nums: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> nums@[k] == kv,
        decreases n - i,
    {
        nums.push(kv);
        i += 1;
    }

    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            n == fillers.len(),
            nums.len() == n + j,
            forall|k: int| 0 <= k < n as int ==> nums@[k] == kv,
            forall|k: int| 0 <= k < j as int ==> nums@[n as int + k] == fillers@[k],
        decreases n - j,
    {
        let v = fillers[j];
        nums.push(v);
        j += 1;
    }

    let two_n: usize = 2 * n;

    proof {
        let s = nums@;
        assert(s.len() == 2 * n);
        // Property 1: 0..n are kv
        assert(forall|k: int| 0 <= k < n as int ==> s[k] == kv);
        // Property 2: n..2n are fillers, hence != kv
        assert forall|k: int| n as int <= k < 2 * n as int implies s[k] != kv by {
            let fi = k - n as int;
            assert(0 <= fi < n as int);
            assert(s[k] == fillers@[fi]);
            assert(fillers@[fi] != kv);
        }

        // count_occ(s, kv) == n
        lemma_all_equal_range(s, kv, n as int);
        assert(count_occ(s, kv) == n as int);
        assert(s.len() / 2 == n as int);

        // For index k = 0, s[0] == kv. Witness.
        assert(s[0] == kv);

        // For each i with s[i] != s[0] (i.e., != kv), count_occ(s, s[i]) == 1
        assert forall|idx: int| 0 <= idx < s.len() && s[idx] != kv
            implies #[trigger] count_occ(s, s[idx]) == 1 by {
            // s[idx] is some filler value
            assert(idx >= n as int);
            let fi = idx - n as int;
            assert(0 <= fi < n as int);
            assert(s[idx] == fillers@[fi]);
            let v = s[idx];
            // v appears exactly at index idx
            // Check all positions in s
            assert forall|p: int| 0 <= p < s.len() && p != idx
                implies s[p] != v by {
                if p < n as int {
                    assert(s[p] == kv);
                    assert(v != kv);
                } else {
                    let fp = p - n as int;
                    assert(0 <= fp < n as int);
                    assert(s[p] == fillers@[fp]);
                    assert(fp != fi);
                    assert(fillers@[fp] != fillers@[fi]);
                }
            }
            assert(s[idx] == v);
            lemma_single_occ(s, v, idx);
        }

        // Witness k=0
        let k0: int = 0;
        assert(0 <= k0 < s.len());
        assert(s[k0] == kv);
        assert(count_occ(s, s[k0]) == s.len() / 2);
        assert(forall|i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] <= 10_000) by {
            assert forall|i: int| 0 <= i < s.len() implies 0 <= #[trigger] s[i] <= 10_000 by {
                if i < n as int {
                    assert(s[i] == kv);
                } else {
                    let fi = i - n as int;
                    assert(s[i] == fillers@[fi]);
                }
            }
        }
        assert(forall|i: int| 0 <= i < s.len() && s[i] != s[k0] ==> #[trigger] count_occ(s, s[i]) == 1);
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

// Generate fillers: n distinct i32 values in [0,10000], all != kv
fn make_fillers(rng: &mut Rng, n: usize, kv: i32, mode: usize) -> Vec<i32> {
    // We need n distinct values, but only 10001 possible values (0..10000).
    // Since n <= 5000, this is feasible.
    let mut used = vec![false; 10_001];
    used[kv as usize] = true;
    let mut res: Vec<i32> = Vec::with_capacity(n);

    match mode % 4 {
        0 => {
            // sequential
            let mut v: i32 = 0;
            while res.len() < n {
                if v >= 0 && v <= 10_000 && !used[v as usize] {
                    used[v as usize] = true;
                    res.push(v);
                }
                v += 1;
                if v > 10_000 { break; }
            }
        }
        1 => {
            // reverse sequential
            let mut v: i32 = 10_000;
            while res.len() < n {
                if v >= 0 && v <= 10_000 && !used[v as usize] {
                    used[v as usize] = true;
                    res.push(v);
                }
                v -= 1;
                if v < 0 { break; }
            }
        }
        2 => {
            // random
            while res.len() < n {
                let v = rng.gen_range_i32(0, 10_000);
                if !used[v as usize] {
                    used[v as usize] = true;
                    res.push(v);
                }
            }
        }
        _ => {
            // clustered around kv
            let mut offset: i32 = 1;
            while res.len() < n {
                let candidates = [kv + offset, kv - offset];
                for &c in &candidates {
                    if c >= 0 && c <= 10_000 && !used[c as usize] && res.len() < n {
                        used[c as usize] = true;
                        res.push(c);
                    }
                }
                offset += 1;
                if offset > 10_001 { break; }
            }
            // fill remaining if any (shouldn't happen for valid n)
            let mut v: i32 = 0;
            while res.len() < n && v <= 10_000 {
                if !used[v as usize] {
                    used[v as usize] = true;
                    res.push(v);
                }
                v += 1;
            }
        }
    }
    res
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
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
        // Choose n (this is the spec "n", and fillers.len() = n, total length = 2n)
        // Constraint: 2 <= n <= 5000
        let n: usize = match mode {
            0 => 2,
            1 => 5000,
            2 => 3,
            3 => 4,
            4 => rng.gen_range_usize(2, 20),
            5 => rng.gen_range_usize(100, 500),
            6 => rng.gen_range_usize(1000, 3000),
            7 => 4999,
            8 => rng.gen_range_usize(2, 5000),
            _ => rng.gen_range_usize(10, 1000),
        };

        // Choose kv
        let kv: i32 = match mode {
            0 => 0,
            1 => 10_000,
            2 => 5000,
            3 => rng.gen_range_i32(0, 10_000),
            4 => rng.gen_range_i32(0, 100),
            5 => rng.gen_range_i32(9900, 10_000),
            _ => rng.gen_range_i32(0, 10_000),
        };

        let fillers = make_fillers(&mut rng, n, kv, mode);
        if fillers.len() != n {
            continue;
        }

        let nums = generate_test_case(kv, fillers);
        print_json(&nums);
    }
}