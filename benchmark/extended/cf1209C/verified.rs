use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn spec_c1_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c1_values(d, c, n - 1);
        if c[n - 1] == 1 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_c2_values(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else {
        let rest = spec_c2_values(d, c, n - 1);
        if c[n - 1] == 2 {
            rest + seq![d[n - 1]]
        } else {
            rest
        }
    }
}

pub open spec fn spec_merged_digits(d: Seq<i32>, c: Seq<i32>, n: int) -> Seq<i32> {
    spec_c1_values(d, c, n) + spec_c2_values(d, c, n)
}

pub open spec fn spec_adjacent_nondecreasing(s: Seq<i32>) -> bool {
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() - 1 ==> s[i] <= s[i + 1]
}

pub open spec fn spec_valid_coloring(d: Seq<i32>, c: Seq<i32>) -> bool {
    d.len() == c.len()
        && (forall|i: int| 0 <= i < d.len() ==> #[trigger] c[i] == 1 || c[i] == 2)
        && spec_adjacent_nondecreasing(spec_merged_digits(d, c, d.len() as int))
}

proof fn lemma_spec_c1_step(d: Seq<i32>, c: Seq<i32>, i: int)
    requires
        0 <= i < d.len(),
        c.len() == d.len(),
    ensures
        spec_c1_values(d, c, i + 1)
            == if c[i] == 1 {
                spec_c1_values(d, c, i) + seq![d[i]]
            } else {
                spec_c1_values(d, c, i)
            },
{
    assert((i + 1) - 1 == i);
    assert(spec_c1_values(d, c, i + 1) == ({
        let rest = spec_c1_values(d, c, i);
        if c[i] == 1 {
            rest + seq![d[i]]
        } else {
            rest
        }
    }));
}

proof fn lemma_spec_c2_step(d: Seq<i32>, c: Seq<i32>, i: int)
    requires
        0 <= i < d.len(),
        c.len() == d.len(),
    ensures
        spec_c2_values(d, c, i + 1)
            == if c[i] == 2 {
                spec_c2_values(d, c, i) + seq![d[i]]
            } else {
                spec_c2_values(d, c, i)
            },
{
    assert((i + 1) - 1 == i);
    assert(spec_c2_values(d, c, i + 1) == ({
        let rest = spec_c2_values(d, c, i);
        if c[i] == 2 {
            rest + seq![d[i]]
        } else {
            rest
        }
    }));
}

proof fn lemma_adjacent_from_prefix(merged: Seq<i32>, n: int)
    requires
        n == merged.len(),
        forall|t: int| #![trigger merged[t]] 0 <= t < n - 1 ==> merged[t] <= merged[t + 1],
    ensures
        spec_adjacent_nondecreasing(merged),
{
}

proof fn lemma_lens_add_n(d: Seq<i32>, c: Seq<i32>, n: int)
    requires
        n >= 0,
        d.len() >= n,
        c.len() >= n,
        forall|i: int| #![trigger c[i]] 0 <= i < n ==> c[i] == 1 || c[i] == 2,
    ensures
        spec_c1_values(d, c, n).len() + spec_c2_values(d, c, n).len() == n,
    decreases n,
{
    if n <= 0 {
    } else {
        lemma_lens_add_n(d, c, n - 1);
        assert(0 <= n - 1 < c.len());
        assert(c[n - 1] == 1 || c[n - 1] == 2);
        let prev_sum = spec_c1_values(d, c, n - 1).len() + spec_c2_values(d, c, n - 1).len();
        let cur_sum = spec_c1_values(d, c, n).len() + spec_c2_values(d, c, n).len();
        assert(cur_sum == prev_sum + 1);
    }
}

pub struct Solution;

impl Solution {
    fn merge_valid(digits: &Vec<i32>, colors: &Vec<i32>, n: usize) -> (b: bool)
        requires
            n == digits.len(),
            n == colors.len(),
            1 <= n <= 200_000,
            forall|j: int|
                #![trigger digits[j]]
                0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
            forall|t: int|
                #![trigger colors[t]]
                0 <= t < n as int ==> #[trigger] colors[t] == 1 || colors[t] == 2,
        ensures
            b ==> spec_adjacent_nondecreasing(spec_merged_digits(digits@, colors@, n as int)),
    {
        let mut merged: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == digits.len(),
                n == colors.len(),
                digits@.len() == n as int,
                colors@.len() == n as int,
                merged@ == spec_c1_values(digits@, colors@, i as int),
            decreases n - i
        {
            proof {
                assert(i < n);
                assert((i as int) < digits@.len());
                assert((i as int) < colors@.len());
                lemma_spec_c1_step(digits@, colors@, i as int);
            }
            if colors[i] == 1 {
                let ghost om = merged@;
                merged.push(digits[i]);
                proof {
                    assert(i < digits.len());
                    assert(merged@ == om.push(digits@[i as int]));
                    let di = digits@[i as int];
                    let tail = seq![di];
                    assert(merged@ == om + tail);
                    let c1_next = spec_c1_values(digits@, colors@, (i + 1) as int);
                    let c1_cur = spec_c1_values(digits@, colors@, i as int);
                    assert(c1_next == c1_cur + tail);
                    assert(merged@ == spec_c1_values(digits@, colors@, (i + 1) as int));
                }
            } else {
                proof {
                    let a = spec_c1_values(digits@, colors@, (i + 1) as int);
                    let b = spec_c1_values(digits@, colors@, i as int);
                    assert(a == b);
                    assert(merged@ == a);
                }
            }
            i = i + 1;
        }
        proof {
            assert(merged@ == spec_c1_values(digits@, colors@, n as int));
        }
        i = 0;
        while i < n
            invariant
                i <= n,
                n == digits.len(),
                n == colors.len(),
                digits@.len() == n as int,
                colors@.len() == n as int,
                merged@ == spec_c1_values(digits@, colors@, n as int) + spec_c2_values(digits@, colors@, i as int),
            decreases n - i
        {
            proof {
                assert(i < n);
                assert((i as int) < digits@.len());
                lemma_spec_c2_step(digits@, colors@, i as int);
            }
            if colors[i] == 2 {
                let ghost om = merged@;
                merged.push(digits[i]);
                proof {
                    assert(i < digits.len());
                    assert(merged@ == om.push(digits@[i as int]));
                    let di = digits@[i as int];
                    let tail = seq![di];
                    assert(merged@ == om + tail);
                    let c2_next = spec_c2_values(digits@, colors@, (i + 1) as int);
                    let c2_cur = spec_c2_values(digits@, colors@, i as int);
                    assert(c2_next == c2_cur + tail);
                    let left = spec_c1_values(digits@, colors@, n as int) + c2_next;
                    let mid = spec_c1_values(digits@, colors@, n as int) + c2_cur;
                    assert(left == mid + tail);
                    assert(merged@ == left);
                }
            } else {
                proof {
                    let ip1 = (i + 1) as int;
                    let s2a = spec_c2_values(digits@, colors@, ip1);
                    let s2b = spec_c2_values(digits@, colors@, i as int);
                    assert(s2a == s2b);
                    let c1n = spec_c1_values(digits@, colors@, n as int);
                    assert(merged@ == c1n + s2a);
                }
            }
            i = i + 1;
        }
        let mlen: usize = merged.len();
        proof {
            assert(merged@ == spec_merged_digits(digits@, colors@, n as int));
            lemma_lens_add_n(digits@, colors@, n as int);
            assert(mlen as int == n as int);
        }
        i = 0;
        while i + 1 < merged.len()
            invariant
                i + 1 <= merged.len(),
                merged.len() == mlen,
                merged@ == spec_merged_digits(digits@, colors@, n as int),
                forall|t: int| #![trigger merged[t]] 0 <= t < i as int ==> merged[t] <= merged[t + 1],
            decreases mlen - 1 - i
        {
            if merged[i] > merged[i + 1] {
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_adjacent_from_prefix(merged@, merged.len() as int);
        }
        true
    }

    fn try_pivot(digits: &Vec<i32>, n: usize, x: i32) -> (r: Vec<i32>)
        requires
            n == digits.len(),
            1 <= n <= 200_000,
            forall|j: int|
                #![trigger digits[j]]
                0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
        ensures
            r.len() == 0 || r.len() == n,
            r.len() == n ==> spec_valid_coloring(digits@, r@),
    {
        let mut last_lt: usize = n;
        let mut i: usize = 0;
        while i < n
            invariant
                n == digits.len(),
                i <= n,
                last_lt <= n,
                last_lt == n || (last_lt as int) < (n as int),
            decreases n - i
        {
            if digits[i] < x {
                last_lt = i;
            }
            i = i + 1;
        }
        let mut colors: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                colors.len() == j,
            decreases n - j
        {
            colors.push(0);
            j = j + 1;
        }
        i = 0;
        while i < n
            invariant
                n == digits.len(),
                i <= n,
                colors.len() == n,
                forall|t: int|
                    #![trigger colors[t]]
                    0 <= t < i as int ==> #[trigger] colors[t] == 1 || colors[t] == 2,
            decreases n - i
        {
            let d = digits[i];
            let c = if d < x {
                1
            } else if d > x {
                2
            } else {
                if last_lt != n && i <= last_lt {
                    2
                } else {
                    1
                }
            };
            colors.set(i, c);
            proof {
                assert(c == 1 || c == 2);
            }
            i = i + 1;
        }
        proof {
            assert(forall|t: int| 0 <= t < n as int ==> colors@[t] == 1 || colors@[t] == 2);
        }
        if Solution::merge_valid(digits, &colors, n) {
            proof {
                assert(spec_adjacent_nondecreasing(spec_merged_digits(digits@, colors@, n as int)));
                assert(spec_valid_coloring(digits@, colors@));
            }
            colors
        } else {
            vec![]
        }
    }

    pub fn paint_digits(digits: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= digits.len() <= 200_000,
            forall|i: int|
                #![trigger digits[i]]
                0 <= i < digits.len() as int ==> 0 <= #[trigger] digits[i] <= 9,
        ensures
            res.len() == 0 || res.len() == digits.len(),
            res.len() == digits.len() ==> spec_valid_coloring(digits@, res@),
    {
        let n = digits.len();
        let mut x: i32 = 0;
        while x <= 9
            invariant
                0 <= x <= 10,
                n == digits.len(),
                1 <= n <= 200_000,
                forall|j: int|
                    #![trigger digits[j]]
                    0 <= j < n as int ==> 0 <= #[trigger] digits[j] <= 9,
            decreases 10 - x
        {
            let cand = Solution::try_pivot(&digits, n, x);
            if cand.len() == n {
                proof {
                    assert(spec_valid_coloring(digits@, cand@));
                }
                return cand;
            }
            x = x + 1;
        }
        vec![]
    }
}

}
