use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_is_one(n: u32, k: int) -> bool {
        0 <= k < 31 && (((n >> (k as u32)) & 1u32) == 1u32)
    }

    pub open spec fn last_one_pos(n: u32, upto: int) -> int
        decreases upto,
    {
        if upto <= 0 {
            -1
        } else if Self::bit_is_one(n, upto - 1) {
            upto - 1
        } else {
            Self::last_one_pos(n, upto - 1)
        }
    }

    pub open spec fn new_gap_at(n: u32, pos: int) -> int {
        let last = Self::last_one_pos(n, pos);
        if last >= 0 { pos - last } else { 0 }
    }

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a > b { a } else { b }
    }

    pub open spec fn binary_gap_prefix(n: u32, upto: int) -> int
        decreases upto,
    {
        if upto <= 0 {
            0
        } else if Self::bit_is_one(n, upto - 1) {
            Self::spec_max(
                Self::binary_gap_prefix(n, upto - 1),
                Self::new_gap_at(n, upto - 1),
            )
        } else {
            Self::binary_gap_prefix(n, upto - 1)
        }
    }

    pub open spec fn binary_gap_spec(n: u32) -> int {
        Self::binary_gap_prefix(n, 31)
    }

    pub proof fn lemma_last_one_pos_step(n: u32, upto: int)
        requires
            0 <= upto < 31,
        ensures
            if Self::bit_is_one(n, upto) {
                Self::last_one_pos(n, upto + 1) == upto
            } else {
                Self::last_one_pos(n, upto + 1) == Self::last_one_pos(n, upto)
            },
    {
        reveal_with_fuel(Solution::last_one_pos, 2);
    }

    pub proof fn lemma_binary_gap_prefix_step(n: u32, upto: int)
        requires
            0 <= upto < 31,
        ensures
            Self::binary_gap_prefix(n, upto + 1) == if Self::bit_is_one(n, upto) {
                Self::spec_max(Self::binary_gap_prefix(n, upto), Self::new_gap_at(n, upto))
            } else {
                Self::binary_gap_prefix(n, upto)
            },
    {
        reveal_with_fuel(Solution::binary_gap_prefix, 2);
    }

    pub fn binary_gap(n: i32) -> (result: i32)
        requires
            1 <= n <= 1_000_000_000,
        ensures
            result as int == Self::binary_gap_spec(n as u32),
    {
        let nu = n as u32;
        let mut m = nu;
        let mut pos: u32 = 0;
        let mut best: u32 = 0;
        let mut last: u32 = 0;
        let mut has_last = false;
        proof {
            assert(m == nu >> pos) by (bit_vector)
                requires
                    m == nu,
                    pos == 0u32,
            {
            }
            assert(Self::binary_gap_prefix(nu, pos as int) == 0);
            assert(Self::last_one_pos(nu, pos as int) == -1);
        }
        while pos < 31u32
            invariant
                1 <= n <= 1_000_000_000,
                nu == n as u32,
                pos <= 31u32,
                m == nu >> pos,
                best as int == Self::binary_gap_prefix(nu, pos as int),
                best <= pos,
                has_last ==> last < pos,
                has_last ==> last as int == Self::last_one_pos(nu, pos as int),
                !has_last ==> Self::last_one_pos(nu, pos as int) == -1,
            decreases 31u32 - pos,
        {
            let ghost old_pos = pos;
            let ghost old_m = m;
            let bit = (m & 1u32) == 1u32;
            proof {
                assert(Self::bit_is_one(nu, pos as int) == (((nu >> pos) & 1u32) == 1u32));
                assert(((nu >> pos) & 1u32) == (m & 1u32)) by (bit_vector)
                    requires
                        pos < 31u32,
                        m == nu >> pos,
                {
                }
                assert((((nu >> pos) & 1u32) == 1u32) == bit);
                assert(Self::bit_is_one(nu, pos as int) == bit);
                Self::lemma_last_one_pos_step(nu, pos as int);
                Self::lemma_binary_gap_prefix_step(nu, pos as int);
            }
            if (m & 1u32) == 1u32 {
                if has_last {
                    let old_best = best;
                    let old_last = last;
                    let gap = pos - last;
                    if gap > best {
                        best = gap;
                    }
                    proof {
                        assert(old_best as int == Self::binary_gap_prefix(nu, pos as int));
                        assert(old_last as int == Self::last_one_pos(nu, pos as int));
                        assert(Self::new_gap_at(nu, pos as int) == pos as int - Self::last_one_pos(nu, pos as int));
                        assert(gap as int == Self::new_gap_at(nu, pos as int));
                        assert(best as int == if gap > old_best { gap } else { old_best });
                        assert(Self::binary_gap_prefix(nu, pos as int + 1) == Self::spec_max(Self::binary_gap_prefix(nu, pos as int), Self::new_gap_at(nu, pos as int)));
                        assert(best as int == Self::binary_gap_prefix(nu, pos as int + 1));
                    }
                } else {
                    proof {
                        assert(Self::last_one_pos(nu, pos as int) == -1);
                        assert(Self::new_gap_at(nu, pos as int) == 0);
                        assert(Self::spec_max(Self::binary_gap_prefix(nu, pos as int), Self::new_gap_at(nu, pos as int)) == Self::binary_gap_prefix(nu, pos as int));
                        assert(Self::binary_gap_prefix(nu, pos as int + 1) == Self::binary_gap_prefix(nu, pos as int));
                        assert(best as int == Self::binary_gap_prefix(nu, pos as int + 1));
                    }
                }
                last = pos;
                has_last = true;
                proof {
                    assert(last as int == pos as int);
                    assert(last as int == Self::last_one_pos(nu, pos as int + 1));
                }
            } else {
                proof {
                    assert(Self::binary_gap_prefix(nu, pos as int + 1) == Self::binary_gap_prefix(nu, pos as int));
                    if has_last {
                        assert(last as int == Self::last_one_pos(nu, pos as int));
                        assert(last as int == Self::last_one_pos(nu, pos as int + 1));
                    } else {
                        assert(Self::last_one_pos(nu, pos as int + 1) == Self::last_one_pos(nu, pos as int));
                        assert(Self::last_one_pos(nu, pos as int + 1) == -1);
                    }
                }
            }
            m = m >> 1u32;
            proof {
                assert((nu >> old_pos) >> 1u32 == nu >> (old_pos + 1u32)) by (bit_vector)
                    requires
                        old_pos < 31u32,
                {
                }
                assert(m == old_m >> 1u32);
                assert(m == nu >> (old_pos + 1u32));
            }
            pos = pos + 1u32;
        }
        proof {
            assert(pos == 31u32);
            assert(best as int == Self::binary_gap_prefix(nu, 31));
        }
        best as i32
    }
}

}
