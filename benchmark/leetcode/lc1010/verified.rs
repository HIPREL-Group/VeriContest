use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_matches(s: Seq<i32>, j: int, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else if (s[j] as int + s[end - 1] as int) % 60 == 0 {
        count_matches(s, j, end - 1) + 1
    } else {
        count_matches(s, j, end - 1)
    }
}

pub open spec fn count_valid_pairs(s: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_valid_pairs(s, n - 1) + count_matches(s, n - 1, n - 1)
    }
}

pub open spec fn count_remainder(s: Seq<i32>, r: int, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else if s[n - 1] as int % 60 == r {
        count_remainder(s, r, n - 1) + 1
    } else {
        count_remainder(s, r, n - 1)
    }
}

proof fn lemma_count_remainder_bounds(s: Seq<i32>, r: int, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        0 <= count_remainder(s, r, n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_remainder_bounds(s, r, n - 1);
    }
}

proof fn lemma_count_matches_bounds(s: Seq<i32>, j: int, end: int)
    requires
        0 <= j < s.len(),
        0 <= end <= s.len(),
    ensures
        0 <= count_matches(s, j, end) <= end,
    decreases end,
{
    if end > 0 {
        lemma_count_matches_bounds(s, j, end - 1);
    }
}

proof fn lemma_count_valid_pairs_nonneg(s: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        0 <= count_valid_pairs(s, n),
    decreases n,
{
    if n > 0 {
        lemma_count_valid_pairs_nonneg(s, n - 1);
        lemma_count_matches_bounds(s, n - 1, n - 1);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_count_valid_pairs_upper(s: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
    ensures
        2 * count_valid_pairs(s, n) <= n * (n - 1),
    decreases n,
{
    if n > 0 {
        lemma_count_valid_pairs_upper(s, n - 1);
        lemma_count_matches_bounds(s, n - 1, n - 1);
        lemma_count_valid_pairs_nonneg(s, n - 1);
        assert(count_valid_pairs(s, n) == count_valid_pairs(s, n - 1) + count_matches(s, n - 1, n - 1));
        assert(2 * count_valid_pairs(s, n - 1) <= (n - 1) * (n - 2));
        assert(0 <= count_matches(s, n - 1, n - 1) <= n - 1);
        assert(2 * count_valid_pairs(s, n) == 2 * count_valid_pairs(s, n - 1) + 2 * count_matches(s, n - 1, n - 1));
        assert(2 * count_valid_pairs(s, n) <= (n - 1) * (n - 2) + 2 * (n - 1));
        assert((n - 1) * (n - 2) + 2 * (n - 1) == n * (n - 1)) by(nonlinear_arith)
            requires
                n >= 1,
        {
        }
        assert(2 * count_valid_pairs(s, n) <= n * (n - 1));
    }
}

proof fn lemma_pair_count_fits_i32(n: int)
    by(nonlinear_arith)
    requires
        0 <= n <= 60_000,
    ensures
        n * (n - 1) < 4_000_000_000,
{
}

proof fn lemma_mod_complement(a: int, b: int)
    requires
        1 <= a <= 500,
        1 <= b <= 500,
    ensures
        (a + b) % 60 == 0 <==> b % 60 == (60 - a % 60) % 60,
{
}

proof fn lemma_matches_equals_remainder(s: Seq<i32>, j: int, end: int)
    requires
        0 <= j < s.len(),
        0 <= end <= j,
        forall|k: int| 0 <= k < s.len() ==> 1 <= #[trigger] s[k] <= 500,
    ensures
        count_matches(s, j, end) == count_remainder(s, (60 - s[j] as int % 60) % 60, end),
    decreases end,
{
    if end > 0 {
        lemma_matches_equals_remainder(s, j, end - 1);
        lemma_mod_complement(s[j] as int, s[end - 1] as int);
    }
}

impl Solution {
    pub fn num_pairs_divisible_by60(time: Vec<i32>) -> (result: i32)
        requires
            1 <= time.len() <= 60_000,
            forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 500,
        ensures
            result as int == count_valid_pairs(time@, time@.len() as int),
    {
        let mut counts: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < 60
            invariant
                0 <= j <= 60,
                counts.len() == j,
                forall|k: int| 0 <= k < j ==> counts[k] == 0i32,
            decreases 60 - j,
        {
            counts.push(0i32);
            j += 1;
        }

        let mut result: i32 = 0;
        let mut i: usize = 0;
        while i < time.len()
            invariant
                0 <= i <= time.len(),
                1 <= time.len() <= 60_000,
                forall|k: int| 0 <= k < time.len() ==> 1 <= #[trigger] time[k] <= 500,
                counts.len() == 60,
                forall|r: int| #![auto] 0 <= r < 60 ==> counts[r] as int == count_remainder(time@, r, i as int),
                result as int == count_valid_pairs(time@, i as int),
                0 <= result,
                forall|r: int| 0 <= r < 60 ==> 0 <= #[trigger] counts[r] <= 60_000,
            decreases time.len() - i,
        {
            let ti = time[i];
            let r = (ti % 60) as usize;
            let comp = ((60 - ti % 60) % 60) as usize;

            proof {
                lemma_matches_equals_remainder(time@, i as int, i as int);
                lemma_count_remainder_bounds(time@, comp as int, i as int);
                assert(count_matches(time@, i as int, i as int) == counts[comp as int] as int);
                assert(result as int + counts[comp as int] as int
                    == count_valid_pairs(time@, i as int) + count_matches(time@, i as int, i as int));
                assert(count_valid_pairs(time@, (i + 1) as int)
                    == count_valid_pairs(time@, i as int) + count_matches(time@, i as int, i as int));
                lemma_count_valid_pairs_upper(time@, (i + 1) as int);
                lemma_count_valid_pairs_nonneg(time@, (i + 1) as int);
                lemma_pair_count_fits_i32((i + 1) as int);
                assert(2 * count_valid_pairs(time@, (i + 1) as int) <= ((i as int) + 1) * (i as int));
                assert(((i as int) + 1) * (i as int) < 4_000_000_000);
                assert(count_valid_pairs(time@, (i + 1) as int) < 2_000_000_000);
            }

            result = result + counts[comp];
            counts.set(r, counts[r] + 1);

            proof {
                assert(time@[i as int] as int % 60 == r as int);
                lemma_count_remainder_bounds(time@, r as int, (i + 1) as int);
            }

            i += 1;
        }
        result
    }
}

}
