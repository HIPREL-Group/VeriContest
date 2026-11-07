use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn MOD() -> int { 1000000007 }

    pub open spec fn sum_zero_prefix(z: int, o: int, limit: int, upto: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
            0 <= upto <= z,
        decreases z + o, 0int, upto when z >= 0 && o >= 0 && 0 <= upto <= z
    {
        if upto <= 0 {
            0
        } else {
            (Self::sum_zero_prefix(z, o, limit, upto - 1) + Self::ways(z - upto, o, limit, false))
                % Self::MOD()
        }
    }

    pub open spec fn sum_one_prefix(z: int, o: int, limit: int, upto: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
            0 <= upto <= o,
        decreases z + o, 0int, upto when z >= 0 && o >= 0 && 0 <= upto <= o
    {
        if upto <= 0 {
            0
        } else {
            (Self::sum_one_prefix(z, o, limit, upto - 1) + Self::ways(z, o - upto, limit, true))
                % Self::MOD()
        }
    }

    pub open spec fn ways(z: int, o: int, limit: int, first_zero: bool) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
        decreases z + o, 1int when z >= 0 && o >= 0
    {
        if z == 0 && o == 0 {
            1
        } else if first_zero {
            Self::sum_zero_prefix(z, o, limit, if z <= limit { z } else { limit })
        } else {
            Self::sum_one_prefix(z, o, limit, if o <= limit { o } else { limit })
        }
    }

    pub open spec fn stable_arrays_mod(z: int, o: int, limit: int) -> int
        recommends
            0 <= z,
            0 <= o,
            1 <= limit,
    {
        (Self::ways(z, o, limit, true) + Self::ways(z, o, limit, false)) % Self::MOD()
    }
}

proof fn lemma_ways_range(z: int, o: int, limit: int, first_zero: bool)
    requires 0 <= z, 0 <= o, 1 <= limit,
    ensures 0 <= Solution::ways(z, o, limit, first_zero) < Solution::MOD(),
    decreases z + o, 1int,
{
    if z == 0 && o == 0 {
    } else if first_zero {
        let upto = if z <= limit { z } else { limit };
        lemma_sum_zero_prefix_range(z, o, limit, upto);
    } else {
        let upto = if o <= limit { o } else { limit };
        lemma_sum_one_prefix_range(z, o, limit, upto);
    }
}

proof fn lemma_sum_zero_prefix_range(z: int, o: int, limit: int, upto: int)
    requires 0 <= z, 0 <= o, 1 <= limit, 0 <= upto <= z,
    ensures 0 <= Solution::sum_zero_prefix(z, o, limit, upto) < Solution::MOD(),
    decreases z + o, 0int, upto,
{
    if upto > 0 {
        lemma_sum_zero_prefix_range(z, o, limit, upto - 1);
        lemma_ways_range(z - upto, o, limit, false);
    }
}

proof fn lemma_sum_one_prefix_range(z: int, o: int, limit: int, upto: int)
    requires 0 <= z, 0 <= o, 1 <= limit, 0 <= upto <= o,
    ensures 0 <= Solution::sum_one_prefix(z, o, limit, upto) < Solution::MOD(),
    decreases z + o, 0int, upto,
{
    if upto > 0 {
        lemma_sum_one_prefix_range(z, o, limit, upto - 1);
        lemma_ways_range(z, o - upto, limit, true);
    }
}

impl Solution {
    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> (result: i32)
        requires
            1 <= zero <= 200,
            1 <= one <= 200,
            1 <= limit <= 200,
        ensures
            result as int == Self::stable_arrays_mod(zero as int, one as int, limit as int),
    {
        let zu: usize = zero as usize;
        let ou: usize = one as usize;
        let limu: usize = limit as usize;
        let md: i64 = 1000000007;

        let mut ways0: Vec<Vec<i64>> = Vec::new();
        let mut ways1: Vec<Vec<i64>> = Vec::new();

        let mut z: usize = 0;
        while z <= zu
            invariant
                zu == zero as int,
                ou == one as int,
                limu == limit as int,
                            md == 1000000007i64,
                1 <= limu,
                ways0.len() == z,
                ways1.len() == z,
                forall |zz: int| 0 <= zz < z ==> ways0[zz].len() == ou + 1,
                forall |zz: int| 0 <= zz < z ==> ways1[zz].len() == ou + 1,
                forall |zz: int, oo: int| 0 <= zz < z && 0 <= oo <= ou ==>
                    #[trigger] ways0[zz][oo] as int == Self::ways(zz, oo, limu as int, true),
                forall |zz: int, oo: int| 0 <= zz < z && 0 <= oo <= ou ==>
                    #[trigger] ways1[zz][oo] as int == Self::ways(zz, oo, limu as int, false),
            decreases zu + 1 - z,
        {
            let mut row0: Vec<i64> = Vec::new();
            let mut row1: Vec<i64> = Vec::new();
            let mut o: usize = 0;
            while o <= ou
                invariant
                    zu == zero as int,
                    ou == one as int,
                    limu == limit as int,
                            md == 1000000007i64,
                    1 <= limu,
                    z <= zu,
                    ways0.len() == z,
                    ways1.len() == z,
                    forall |zz: int| 0 <= zz < z ==> ways0[zz].len() == ou + 1,
                    forall |zz: int| 0 <= zz < z ==> ways1[zz].len() == ou + 1,
                    forall |zz: int, oo: int| 0 <= zz < z && 0 <= oo <= ou ==>
                        #[trigger] ways0[zz][oo] as int == Self::ways(zz, oo, limu as int, true),
                    forall |zz: int, oo: int| 0 <= zz < z && 0 <= oo <= ou ==>
                        #[trigger] ways1[zz][oo] as int == Self::ways(zz, oo, limu as int, false),
                    o <= ou + 1,
                    row0.len() == o,
                    row1.len() == o,
                    forall |oo: int| 0 <= oo < o ==> #[trigger] row0[oo] as int == Self::ways(z as int, oo, limu as int, true),
                    forall |oo: int| 0 <= oo < o ==> #[trigger] row1[oo] as int == Self::ways(z as int, oo, limu as int, false),
                decreases ou + 1 - o,
            {
                if z == 0 && o == 0 {
                    row0.push(1);
                    row1.push(1);
                    proof {
                        assert(Self::ways(0, 0, limu as int, true) == 1);
                        assert(Self::ways(0, 0, limu as int, false) == 1);
                    }
                } else {
                    let upto0: usize = if z <= limu { z } else { limu };
                    let mut s0: i64 = 0;
                    let mut u: usize = 1;
                    proof {
                        assert(Self::sum_zero_prefix(z as int, o as int, limu as int, 0) == 0);
                    }
                    while u <= upto0
                        invariant
                            zu == zero as int,
                            ou == one as int,
                            limu == limit as int,
                            md == 1000000007i64,
                            1 <= limu,
                            z <= zu,
                            0 <= z, 0 <= o <= ou,
                            upto0 == (if z <= limu { z } else { limu }),
                            1 <= u <= upto0 + 1,
                            ways0.len() == z,
                            ways1.len() == z,
                            forall |zz: int| 0 <= zz < z ==> ways1[zz].len() == ou + 1,
                            forall |zz: int, oo: int| 0 <= zz < z && 0 <= oo <= ou ==>
                                #[trigger] ways1[zz][oo] as int == Self::ways(zz, oo, limu as int, false),
                            s0 as int == Self::sum_zero_prefix(z as int, o as int, limu as int, u as int - 1),
                            0 <= s0 < 1000000007,
                        decreases upto0 + 1 - u,
                    {
                        let idx0: usize = z - u;
                        let term_val: i64 = ways1[idx0][o];
                        let ghost s0_old = s0 as int;
                        proof {
                            assert(idx0 as int == z as int - u as int);
                            assert(0 <= idx0 as int);
                            assert((idx0 as int) < (z as int));
                            assert(Self::sum_zero_prefix(z as int, o as int, limu as int, u as int)
                                == (Self::sum_zero_prefix(z as int, o as int, limu as int, u as int - 1)
                                    + Self::ways(idx0 as int, o as int, limu as int, false)) % Self::MOD());
                            lemma_ways_range(idx0 as int, o as int, limu as int, false);
                            assert(term_val as int == Self::ways(idx0 as int, o as int, limu as int, false));
                            assert(0 <= term_val < 1000000007);
                            assert(0 <= s0 + term_val);
                            assert(s0 + term_val < 2 * 1000000007);
                            assert(md == 1000000007i64);
                        }
                        s0 = (s0 + term_val) % md;
                        proof {
                            assert(s0 as int == (s0_old + term_val as int) % 1000000007int);
                            assert(s0 as int == Self::sum_zero_prefix(z as int, o as int, limu as int, u as int));
                        }
                        u += 1;
                    }
                    row0.push(s0);
                    proof {
                        assert(upto0 as int == (if z as int <= limu as int { z as int } else { limu as int }));
                        assert(Self::ways(z as int, o as int, limu as int, true)
                            == Self::sum_zero_prefix(z as int, o as int, limu as int, upto0 as int));
                    }

                    let upto1: usize = if o <= limu { o } else { limu };
                    let mut s1: i64 = 0;
                    let mut u2: usize = 1;
                    proof {
                        assert(Self::sum_one_prefix(z as int, o as int, limu as int, 0) == 0);
                    }
                    while u2 <= upto1
                        invariant
                            zu == zero as int,
                            ou == one as int,
                            limu == limit as int,
                            md == 1000000007i64,
                            1 <= limu,
                            z <= zu,
                            0 <= z, 0 <= o <= ou,
                            upto1 == (if o <= limu { o } else { limu }),
                            1 <= u2 <= upto1 + 1,
                            row0.len() == o + 1,
                            forall |oo: int| 0 <= oo < o ==> #[trigger] row0[oo] as int == Self::ways(z as int, oo, limu as int, true),
                            s1 as int == Self::sum_one_prefix(z as int, o as int, limu as int, u2 as int - 1),
                            0 <= s1 < 1000000007,
                        decreases upto1 + 1 - u2,
                    {
                        let idx1: usize = o - u2;
                        let term_val1: i64 = row0[idx1];
                        let ghost s1_old = s1 as int;
                        proof {
                            assert(idx1 as int == o as int - u2 as int);
                            assert(0 <= idx1 as int);
                            assert((idx1 as int) < (o as int));
                            assert(Self::sum_one_prefix(z as int, o as int, limu as int, u2 as int)
                                == (Self::sum_one_prefix(z as int, o as int, limu as int, u2 as int - 1)
                                    + Self::ways(z as int, idx1 as int, limu as int, true)) % Self::MOD());
                            lemma_ways_range(z as int, idx1 as int, limu as int, true);
                            assert(term_val1 as int == Self::ways(z as int, idx1 as int, limu as int, true));
                            assert(0 <= term_val1 < 1000000007);
                            assert(0 <= s1 + term_val1);
                            assert(s1 + term_val1 < 2 * 1000000007);
                            assert(md == 1000000007i64);
                        }
                        s1 = (s1 + term_val1) % md;
                        proof {
                            assert(s1 as int == (s1_old + term_val1 as int) % 1000000007int);
                            assert(s1 as int == Self::sum_one_prefix(z as int, o as int, limu as int, u2 as int));
                        }
                        u2 += 1;
                    }
                    row1.push(s1);
                    proof {
                        assert(upto1 as int == (if o as int <= limu as int { o as int } else { limu as int }));
                        assert(Self::ways(z as int, o as int, limu as int, false)
                            == Self::sum_one_prefix(z as int, o as int, limu as int, upto1 as int));
                    }
                }
                o += 1;
            }
            proof {
                assert forall |oo: int| 0 <= oo <= ou as int implies row0[oo] as int == Self::ways(z as int, oo, limu as int, true) by {}
                assert forall |oo: int| 0 <= oo <= ou as int implies row1[oo] as int == Self::ways(z as int, oo, limu as int, false) by {}
            }
            let ghost old_z = z as int;
            let ghost old_ways0 = ways0@;
            let ghost old_ways1 = ways1@;
            let ghost row0_ghost = row0@;
            let ghost row1_ghost = row1@;
            ways0.push(row0);
            ways1.push(row1);
            proof {
                assert(ways0@.len() == old_ways0.len() + 1);
                assert(ways1@.len() == old_ways1.len() + 1);
                assert(ways0@[old_z]@ =~= row0_ghost);
                assert(ways1@[old_z]@ =~= row1_ghost);
                assert(row0_ghost.len() == ou as int + 1);
                assert(row1_ghost.len() == ou as int + 1);
                assert(ways0@[old_z]@.len() == ou as int + 1);
                assert(ways1@[old_z]@.len() == ou as int + 1);
                assert forall |zz: int| 0 <= zz < old_z + 1 implies ways0[zz].len() == ou + 1 by {}
                assert forall |zz: int| 0 <= zz < old_z + 1 implies ways1[zz].len() == ou + 1 by {}
                assert forall |zz: int, oo: int| 0 <= zz < old_z && 0 <= oo <= ou implies
                    #[trigger] ways0[zz][oo] as int == Self::ways(zz, oo, limu as int, true) by {}
                assert forall |zz: int, oo: int| 0 <= zz < old_z && 0 <= oo <= ou implies
                    #[trigger] ways1[zz][oo] as int == Self::ways(zz, oo, limu as int, false) by {}
                assert forall |oo: int| 0 <= oo <= ou as int implies
                    #[trigger] ways0[old_z][oo] as int == Self::ways(old_z, oo, limu as int, true) by {}
                assert forall |oo: int| 0 <= oo <= ou as int implies
                    #[trigger] ways1[old_z][oo] as int == Self::ways(old_z, oo, limu as int, false) by {}
            }
            z += 1;
        }

        let a = ways0[zu][ou];
        let b = ways1[zu][ou];
        proof {
            assert(a as int == Self::ways(zu as int, ou as int, limu as int, true));
            assert(b as int == Self::ways(zu as int, ou as int, limu as int, false));
            lemma_ways_range(zu as int, ou as int, limu as int, true);
            lemma_ways_range(zu as int, ou as int, limu as int, false);
        }
        let result = ((a + b) % md) as i32;
        proof {
            assert(result as int == (a as int + b as int) % Self::MOD());
            assert(result as int == Self::stable_arrays_mod(zu as int, ou as int, limu as int));
        }
        result
    }
}

}
