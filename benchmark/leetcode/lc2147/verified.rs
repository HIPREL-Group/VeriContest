use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seat_count_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0int
        } else {
            Self::seat_count_prefix(s, n - 1) + if s[n - 1] == 'S' { 1int } else { 0int }
        }
    }

    pub open spec fn plants_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0int
        } else {
            let prev_seats = Self::seat_count_prefix(s, n - 1);
            if s[n - 1] == 'P' && prev_seats >= 2 && prev_seats % 2 == 0 {
                Self::plants_prefix(s, n - 1) + 1
            } else {
                0int
            }
        }
    }

    pub open spec fn ways_prefix(s: Seq<char>, n: int) -> int
        decreases n
    {
        if n <= 0 {
            1
        } else {
            let prev = Self::ways_prefix(s, n - 1);
            let prev_seats = Self::seat_count_prefix(s, n - 1);
            if s[n - 1] == 'S' && prev_seats >= 2 && prev_seats % 2 == 0 {
                (prev * (Self::plants_prefix(s, n - 1) + 1)) % 1_000_000_007
            } else {
                prev
            }
        }
    }

    pub open spec fn number_of_ways_spec(s: Seq<char>) -> int {
        let seats = Self::seat_count_prefix(s, s.len() as int);
        if seats == 0 || seats % 2 == 1 {
            0
        } else {
            Self::ways_prefix(s, s.len() as int)
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn number_of_ways(corridor: String) -> (result: i32)
        requires
            1 <= corridor@.len() <= 100_000,
            forall |i: int| 0 <= i < corridor@.len() ==> corridor@[i] == 'S' || corridor@[i] == 'P',
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::number_of_ways_spec(corridor@),
    {
        let mod_num: u128 = 1_000_000_007;
        let len = corridor.as_str().unicode_len();
        let mut seat_count: usize = 0;
        let mut plants: usize = 0;
        let mut ways: u128 = 1;
        let mut i: usize = 0;

        while i < len
            invariant
                mod_num == 1_000_000_007u128,
                len == corridor@.len(),
                0 <= i <= len,
                1 <= len <= 100_000,
                forall |k: int| 0 <= k < corridor@.len() ==> corridor@[k] == 'S' || corridor@[k] == 'P',
                seat_count as int == Self::seat_count_prefix(corridor@, i as int),
                0 <= seat_count as int <= i as int,
                plants as int == Self::plants_prefix(corridor@, i as int),
                0 <= plants as int <= i as int,
                0 <= ways < mod_num,
                ways as int == Self::ways_prefix(corridor@, i as int),
            decreases len - i,
        {
            let c = corridor.as_str().get_char(i);
            proof {
                assert(corridor@[i as int] == c);
            }
            if c == 'S' {
                if seat_count >= 2 && seat_count % 2 == 0 {
                    let sep = plants + 1;
                    proof {
                        assert(sep == plants + 1);
                        assert(1 <= sep) by (nonlinear_arith)
                            requires
                                sep == plants + 1,
                        {};
                        assert(sep <= len) by (nonlinear_arith)
                            requires
                                sep == plants + 1,
                                plants as int <= i as int,
                                i < len,
                        {};
                        assert(ways * (sep as u128) < 340_282_366_920_938_463_463_374_607_431_768_211_455u128) by (nonlinear_arith)
                            requires
                                0 <= ways < mod_num,
                                1 <= sep,
                                sep <= len,
                                len <= 100_000,
                                mod_num == 1_000_000_007u128,
                        {};
                    }
                    let prod = ways * sep as u128;
                    let new_ways = prod % mod_num;
                    proof {
                        assert(corridor@[i as int] == 'S');
                        assert(sep == plants + 1);
                        assert(sep as int == plants as int + 1) by (nonlinear_arith)
                            requires
                                sep == plants + 1,
                        {};
                        assert(sep as int == Self::plants_prefix(corridor@, i as int) + 1) by (nonlinear_arith)
                            requires
                                sep as int == plants as int + 1,
                                plants as int == Self::plants_prefix(corridor@, i as int),
                        {};
                        assert(new_ways as int
                            == ((ways as int) * (sep as int)) % 1_000_000_007int) by (nonlinear_arith)
                            requires
                                new_ways == prod % mod_num,
                                prod == ways * (sep as u128),
                                0 <= ways < mod_num,
                                1 <= sep,
                                sep <= len,
                                len <= 100_000,
                                mod_num == 1_000_000_007u128,
                        {};
                        assert(Self::ways_prefix(corridor@, i as int + 1)
                            == (Self::ways_prefix(corridor@, i as int)
                                * (Self::plants_prefix(corridor@, i as int) + 1)) % 1_000_000_007);
                        assert(new_ways as int
                            == (Self::ways_prefix(corridor@, i as int)
                                * (Self::plants_prefix(corridor@, i as int) + 1)) % 1_000_000_007int) by (nonlinear_arith)
                            requires
                                0 <= ways < mod_num,
                                new_ways as int == (prod as int) % 1_000_000_007int,
                                prod as int == (ways as int) * (sep as int),
                                ways as int == Self::ways_prefix(corridor@, i as int),
                                sep as int == Self::plants_prefix(corridor@, i as int) + 1,
                                mod_num == 1_000_000_007u128,
                        {};
                    }
                    ways = new_ways;
                }
                proof {
                    assert(seat_count < 100_000usize) by (nonlinear_arith)
                        requires
                            seat_count as int <= i as int,
                            i < len,
                            len <= 100_000,
                    {};
                    assert(Self::seat_count_prefix(corridor@, i as int + 1) == Self::seat_count_prefix(corridor@, i as int) + 1);
                    assert(Self::plants_prefix(corridor@, i as int + 1) == 0);
                    if !(seat_count >= 2 && seat_count % 2 == 0) {
                        assert(Self::ways_prefix(corridor@, i as int + 1) == Self::ways_prefix(corridor@, i as int));
                    }
                }
                seat_count += 1;
                plants = 0;
            } else {
                if seat_count >= 2 && seat_count % 2 == 0 {
                    proof {
                        assert(corridor@[i as int] == 'P');
                        assert(Self::seat_count_prefix(corridor@, i as int + 1) == Self::seat_count_prefix(corridor@, i as int));
                        assert(Self::plants_prefix(corridor@, i as int + 1) == Self::plants_prefix(corridor@, i as int) + 1);
                        assert(Self::ways_prefix(corridor@, i as int + 1) == Self::ways_prefix(corridor@, i as int));
                    }
                    plants += 1;
                } else {
                    proof {
                        assert(corridor@[i as int] == 'P');
                        assert(Self::seat_count_prefix(corridor@, i as int + 1) == Self::seat_count_prefix(corridor@, i as int));
                        assert(Self::plants_prefix(corridor@, i as int + 1) == 0);
                        assert(Self::ways_prefix(corridor@, i as int + 1) == Self::ways_prefix(corridor@, i as int));
                    }
                }
            }
            i += 1;
        }

        proof {
            assert(seat_count == Self::seat_count_prefix(corridor@, len as int));
            assert(ways as int == Self::ways_prefix(corridor@, len as int));
        }
        if seat_count == 0 || seat_count % 2 == 1 {
            proof {
                assert(Self::number_of_ways_spec(corridor@) == 0);
            }
            0
        } else {
            proof {
                assert(ways <= 2_147_483_647u128) by (nonlinear_arith)
                    requires
                        0 <= ways < mod_num,
                        mod_num == 1_000_000_007u128,
                {};
                assert(Self::seat_count_prefix(corridor@, len as int) == seat_count);
                assert(Self::seat_count_prefix(corridor@, len as int) != 0);
                assert(Self::seat_count_prefix(corridor@, len as int) % 2 != 1);
                assert(Self::number_of_ways_spec(corridor@) == Self::ways_prefix(corridor@, len as int));
            }
            ways as i32
        }
    }
}

}
