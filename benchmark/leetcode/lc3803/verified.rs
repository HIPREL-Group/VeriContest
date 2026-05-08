use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_lowercase_string(s: Seq<char>) -> bool {
        forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
    }

    pub open spec fn is_first_occurrence(s: Seq<char>, idx: nat) -> bool
        recommends
            idx < s.len(),
    {
        forall |q: int| 0 <= q < idx ==> s[q] != s[idx as int]
    }

    pub open spec fn distinct_count_prefix(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::distinct_count_prefix(s, (n - 1) as nat)
                + (if Self::is_first_occurrence(s, (n - 1) as nat) { 1int } else { 0int })
        }
    }

    pub open spec fn residue_prefix_count(s: Seq<char>, n: nat) -> int
        recommends
            n <= s.len(),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            Self::residue_prefix_count(s, (n - 1) as nat)
                + (if Self::distinct_count_prefix(s, n) == (n as int) % 3 { 1int } else { 0int })
        }
    }

    proof fn lemma_distinct_step(s: Seq<char>, n: nat)
        requires
            n < s.len(),
        ensures
            Self::distinct_count_prefix(s, (n + 1) as nat)
                == Self::distinct_count_prefix(s, n)
                    + (if Self::is_first_occurrence(s, n) { 1int } else { 0int }),
    {
    }

    proof fn lemma_residue_step(s: Seq<char>, n: nat)
        requires
            n < s.len(),
        ensures
            Self::residue_prefix_count(s, (n + 1) as nat)
                == Self::residue_prefix_count(s, n)
                    + (if Self::distinct_count_prefix(s, (n + 1) as nat) == ((n + 1) as int) % 3 { 1int } else { 0int }),
    {
    }

    proof fn lemma_distinct_bound(s: Seq<char>, n: nat)
        requires
            n <= s.len(),
        ensures
            0 <= Self::distinct_count_prefix(s, n) <= n as int,
        decreases n,
    {
        if n > 0 {
            let m = (n - 1) as nat;
            Self::lemma_distinct_bound(s, m);
            Self::lemma_distinct_step(s, m);
        }
    }

    proof fn lemma_residue_bound(s: Seq<char>, n: nat)
        requires
            n <= s.len(),
        ensures
            0 <= Self::residue_prefix_count(s, n) <= n as int,
        decreases n,
    {
        if n > 0 {
            let m = (n - 1) as nat;
            Self::lemma_residue_bound(s, m);
            Self::lemma_distinct_bound(s, n);
            Self::lemma_residue_step(s, m);
        }
    }

    fn is_first_at(s: &String, p: usize) -> (res: bool)
        requires
            p < s@.len(),
        ensures
            res <==> Self::is_first_occurrence(s@, p as nat),
    {
        let mut q: usize = 0;
        while q < p
            invariant
                p < s@.len(),
                0 <= q <= p,
                forall |t: int| 0 <= t < q as int ==> s@[t] != s@[p as int],
            decreases p - q,
        {
            let cq = s.as_str().get_char(q);
            let cp = s.as_str().get_char(p);
            if s.as_str().get_char(q) == s.as_str().get_char(p) {
                assert(cq == cp);
                proof {
                    assert(s@[q as int] == cq);
                    assert(s@[p as int] == cp);
                    assert(!(forall |u: int| 0 <= u < p as int ==> s@[u] != s@[p as int])) by {
                        let u = q as int;
                        assert(0 <= u < p as int);
                        assert(s@[u] == s@[p as int]);
                    }
                    assert(!Self::is_first_occurrence(s@, p as nat));
                }
                return false;
            }
            q += 1;
        }
        proof {
            assert(q == p);
            assert(forall |t: int| 0 <= t < p as int ==> s@[t] != s@[p as int]);
            assert(Self::is_first_occurrence(s@, p as nat));
        }
        true
    }

    pub fn residue_prefixes(s: String) -> (res: i32)
        requires
            1 <= s@.len() <= 100,
            Self::is_lowercase_string(s@),
        ensures
            res as int == Self::residue_prefix_count(s@, s@.len()),
    {
        proof {
            Self::lemma_residue_bound(s@, s@.len());
        }
        let n = s.as_str().unicode_len();
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= s@.len() <= 100,
                Self::is_lowercase_string(s@),
                n == s@.len(),
                0 <= i <= n,
                ans as int == Self::residue_prefix_count(s@, i as nat),
                0 <= ans <= i as int,
            decreases n - i,
        {
            let mut distinct: i32 = 0;
            let mut p: usize = 0;
            while p <= i
                invariant
                    1 <= s@.len() <= 100,
                    n == s@.len(),
                    i < n,
                    0 <= p <= i + 1,
                    distinct as int == Self::distinct_count_prefix(s@, p as nat),
                    0 <= distinct <= p as int,
                decreases i + 1 - p,
            {
                let is_new = Self::is_first_at(&s, p);
                let ghost d_before = distinct;
                proof {
                    Self::lemma_distinct_bound(s@, p as nat);
                    assert(d_before as int == Self::distinct_count_prefix(s@, p as nat));
                    assert(0 <= d_before <= p as int);
                }
                if is_new {
                    distinct += 1;
                }
                proof {
                    Self::lemma_distinct_step(s@, p as nat);
                    if is_new {
                        assert(Self::is_first_occurrence(s@, p as nat));
                        assert(distinct as int == d_before as int + 1);
                    } else {
                        assert(!Self::is_first_occurrence(s@, p as nat));
                        assert(distinct as int == d_before as int);
                    }
                    assert(distinct as int == Self::distinct_count_prefix(s@, (p + 1) as nat));
                    Self::lemma_distinct_bound(s@, (p + 1) as nat);
                    assert(0 <= distinct <= (p + 1) as int);
                }
                p += 1;
            }

            let residue: i32 = ((i + 1) % 3) as i32;
            let ghost ans_before = ans;
            if distinct == residue {
                ans += 1;
            }
            proof {
                let ii = i as nat;
                Self::lemma_residue_step(s@, ii);
                assert(ans_before as int == Self::residue_prefix_count(s@, ii));
                assert(distinct as int == Self::distinct_count_prefix(s@, (ii + 1) as nat));
                assert(residue as int == ((ii + 1) as int) % 3);
                if distinct == residue {
                    assert(Self::distinct_count_prefix(s@, (ii + 1) as nat) == ((ii + 1) as int) % 3);
                    assert(ans as int == ans_before as int + 1);
                } else {
                    assert(Self::distinct_count_prefix(s@, (ii + 1) as nat) != ((ii + 1) as int) % 3);
                    assert(ans as int == ans_before as int);
                }
                assert(ans as int == Self::residue_prefix_count(s@, (ii + 1) as nat));
                Self::lemma_residue_bound(s@, (ii + 1) as nat);
                assert(0 <= ans <= (ii + 1) as int);
            }
            i += 1;
        }

        ans
    }
}

}
