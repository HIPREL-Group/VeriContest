use vstd::prelude::*;

verus! {

pub open spec fn appears_in_spec(s: Seq<i32>, val: i32) -> bool {
    exists |j: int| 0 <= j < s.len() && #[trigger] s[j] == val
}

pub open spec fn appears_twice_spec(s: Seq<i32>, val: i32) -> bool {
    exists |j1: int, j2: int| 0 <= j1 < j2 < s.len()
        && #[trigger] s[j1] == val && #[trigger] s[j2] == val
}

// Build nums by: n in [2, 10_000]; values[0..n] is a permutation of 1..=n
// except one index `dup_idx` holds `dup_val` (a value already in the array)
// instead of `missing`.
// Concretely: construct nums[i] for i in 0..n as follows:
//   if i == dup_idx { dup_val } else if (i+1) == missing { dup_val } else { (i+1) as i32 }
// Wait we need two occurrences of dup_val.
//
// Simpler construction: start with nums[i] = (i+1) for all i in 0..n.
// Then replace nums[missing-1] with dup_val. Since missing != dup_val,
// position (dup_val - 1) still holds dup_val, and position (missing-1) now holds dup_val.
// So dup_val appears twice, missing doesn't appear.

pub fn generate_test_case(n: usize, dup_val: i32, missing: i32) -> (nums: Vec<i32>)
    requires
        2 <= n <= 10_000,
        1 <= dup_val <= n as i32,
        1 <= missing <= n as i32,
        dup_val != missing,
    ensures
        2 <= nums.len() <= 10_000,
        nums.len() == n,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
        exists |d: int| 1 <= d <= nums.len() && #[trigger] appears_twice_spec(nums@, d as i32),
        exists |m: int| 1 <= m <= nums.len() && !#[trigger] appears_in_spec(nums@, m as i32),
        forall |v1: i32, v2: i32|
            appears_twice_spec(nums@, v1) && appears_twice_spec(nums@, v2) ==> v1 == v2,
        forall |v1: int, v2: int|
            1 <= v1 <= nums.len() && 1 <= v2 <= nums.len()
            && !#[trigger] appears_in_spec(nums@, v1 as i32) && !#[trigger] appears_in_spec(nums@, v2 as i32)
            ==> v1 == v2,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            2 <= n <= 10_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == (k + 1) as i32,
        decreases n - i,
    {
        nums.push((i + 1) as i32);
        i = i + 1;
    }

    // Now nums[k] == k+1 for all k.
    let missing_idx: usize = (missing - 1) as usize;
    let dup_idx: usize = (dup_val - 1) as usize;

    assert(missing_idx < n);
    assert(dup_idx < n);
    assert(missing_idx != dup_idx);
    assert(nums[dup_idx as int] == dup_val);
    assert(nums[missing_idx as int] == missing);

    nums.set(missing_idx, dup_val);

    proof {
        // After set: nums[missing_idx] = dup_val, nums[dup_idx] unchanged = dup_val, others unchanged = k+1.
        assert(nums.len() == n);
        assert(nums[dup_idx as int] == dup_val);
        assert(nums[missing_idx as int] == dup_val);

        assert forall |k: int| 0 <= k < nums.len() implies 1 <= #[trigger] nums[k] <= nums.len() by {
            if k == missing_idx as int {
                assert(nums[k] == dup_val);
            } else {
                assert(nums[k] == (k + 1) as i32);
            }
        }

        // dup_val appears twice
        let j1: int = if (dup_idx as int) < (missing_idx as int) { dup_idx as int } else { missing_idx as int };
        let j2: int = if (dup_idx as int) < (missing_idx as int) { missing_idx as int } else { dup_idx as int };
        assert(0 <= j1 < j2 < nums.len());
        assert(nums[j1] == dup_val);
        assert(nums[j2] == dup_val);
        assert(appears_twice_spec(nums@, dup_val));
        assert(exists |d: int| 1 <= d <= nums.len() && #[trigger] appears_twice_spec(nums@, d as i32)) by {
            assert(1 <= dup_val as int <= nums.len());
            assert(appears_twice_spec(nums@, dup_val as int as i32));
        }

        // missing does not appear
        assert forall |k: int| 0 <= k < nums.len() implies #[trigger] nums[k] != missing by {
            if k == missing_idx as int {
                assert(nums[k] == dup_val);
                assert(dup_val != missing);
            } else {
                assert(nums[k] == (k + 1) as i32);
                if (k + 1) as i32 == missing {
                    assert(k == missing_idx as int);
                }
            }
        }
        assert(!appears_in_spec(nums@, missing));
        assert(exists |m: int| 1 <= m <= nums.len() && !#[trigger] appears_in_spec(nums@, m as i32)) by {
            assert(1 <= missing as int <= nums.len());
            assert(!appears_in_spec(nums@, missing as int as i32));
        }

        // Uniqueness of twice-appearing value: if v appears twice, then v == dup_val.
        assert forall |v: i32| appears_twice_spec(nums@, v) implies v == dup_val by {
            // There exist j1 < j2 with nums[j1]==v and nums[j2]==v.
            let (a, b): (int, int) = choose |a: int, b: int| 0 <= a < b < nums@.len()
                && #[trigger] nums@[a] == v && #[trigger] nums@[b] == v;
            // For any index k other than missing_idx, nums[k] == k+1 which is unique.
            // So both a and b have same value only if one of them is missing_idx.
            if a == missing_idx as int {
                assert(nums[a] == dup_val);
                assert(v == dup_val);
            } else if b == missing_idx as int {
                assert(nums[b] == dup_val);
                assert(v == dup_val);
            } else {
                assert(nums[a] == (a + 1) as i32);
                assert(nums[b] == (b + 1) as i32);
                assert(a + 1 == b + 1);
                assert(false);
            }
        }

        assert forall |v1: i32, v2: i32|
            appears_twice_spec(nums@, v1) && appears_twice_spec(nums@, v2) implies v1 == v2 by {
            assert(v1 == dup_val);
            assert(v2 == dup_val);
        }

        // Uniqueness of missing value
        assert forall |v1: int, v2: int|
            1 <= v1 <= nums.len() && 1 <= v2 <= nums.len()
            && !#[trigger] appears_in_spec(nums@, v1 as i32) && !#[trigger] appears_in_spec(nums@, v2 as i32)
            implies v1 == v2 by {
            // For any x in 1..=n with x != missing, x appears in nums at index x-1 (if x != missing)
            // or ... actually if x != missing and x != dup_val-replaced. Let's just prove it appears.
            if v1 != missing as int {
                let idx1: int = v1 - 1;
                assert(0 <= idx1 < nums.len());
                if idx1 == missing_idx as int {
                    assert(v1 == missing as int);
                    assert(false);
                } else {
                    assert(nums[idx1] == (idx1 + 1) as i32);
                    assert(nums[idx1] == v1 as i32);
                    assert(appears_in_spec(nums@, v1 as i32));
                    assert(false);
                }
            }
            if v2 != missing as int {
                let idx2: int = v2 - 1;
                assert(0 <= idx2 < nums.len());
                if idx2 == missing_idx as int {
                    assert(v2 == missing as int);
                    assert(false);
                } else {
                    assert(nums[idx2] == (idx2 + 1) as i32);
                    assert(nums[idx2] == v2 as i32);
                    assert(appears_in_spec(nums@, v2 as i32));
                    assert(false);
                }
            }
            assert(v1 == missing as int);
            assert(v2 == missing as int);
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
}

fn pick_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, i32) {
    // returns (n, dup_val, missing)
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => 10_000,
        3 => 9_999,
        4 => 2 + (t % 8),
        5 => 100 + (t % 50),
        6 => 500,
        7 => 1000 + (t % 200),
        8 => 5000,
        9 => 10_000,
        _ => 10 + rng.gen_range_usize(0, 200),
    };

    let (dup_val, missing) = match mode {
        0 => {
            // smallest case, dup=1, missing=2 or dup=2, missing=1
            if t % 2 == 0 { (1i32, 2i32) } else { (2i32, 1i32) }
        }
        1 => {
            // dup = missing + 1 or similar
            (1i32, 3i32)
        }
        2 => {
            // large n, dup = 1, missing = n
            (1i32, n as i32)
        }
        3 => {
            // large n, dup = n, missing = 1
            (n as i32, 1i32)
        }
        4 => {
            // random pair
            let a = rng.gen_range_usize(1, n) as i32;
            let mut b = rng.gen_range_usize(1, n - 1) as i32;
            if b >= a { b += 1; }
            (a, b)
        }
        5 => {
            // dup near middle
            let m = (n / 2) as i32;
            let miss = if m == 1 { 2i32 } else { m - 1 };
            (m, miss)
        }
        6 => {
            // dup and missing adjacent
            let a = rng.gen_range_usize(1, n - 1) as i32;
            (a, a + 1)
        }
        7 => {
            // dup = missing - 1? No, must differ. dup small, missing large
            (2i32, (n - 1) as i32)
        }
        8 => {
            // dup = largest, missing = middle
            (n as i32, (n / 2) as i32)
        }
        9 => {
            // boundary: dup=1, missing=n
            (1i32, n as i32)
        }
        _ => {
            let a = rng.gen_range_usize(1, n) as i32;
            let mut b = rng.gen_range_usize(1, n - 1) as i32;
            if b >= a { b += 1; }
            (a, b)
        }
    };

    // Sanity: ensure dup_val != missing and both in [1, n]
    let dv = if dup_val < 1 { 1 } else if dup_val > n as i32 { n as i32 } else { dup_val };
    let mut ms = if missing < 1 { 1 } else if missing > n as i32 { n as i32 } else { missing };
    if ms == dv {
        ms = if dv == 1 { 2 } else { 1 };
    }
    (n, dv, ms)
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, dup_val, missing) = pick_case(&mut rng, mode, t);
        let nums = generate_test_case(n, dup_val, missing);
        print_json(&nums);
    }
}