use vstd::arithmetic::mul::lemma_mul_upper_bound;
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_factor_at(a: Seq<i64>, bump: int, k: int) -> int
    recommends
        0 <= k && k < a.len(),
{
    if k == bump {
        a[k] as int + 1
    } else {
        a[k] as int
    }
}

pub open spec fn spec_prefix_with_bump(a: Seq<i64>, bump: int, until: int) -> int
    recommends
        0 <= until && until <= a.len() && a.len() <= 9,
{
    if until == 0 {
        1
    } else if until == 1 {
        spec_factor_at(a, bump, 0)
    } else if until == 2 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1)
    } else if until == 3 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
    } else if until == 4 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3)
    } else if until == 5 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4)
    } else if until == 6 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
    } else if until == 7 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6)
    } else if until == 8 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6) * spec_factor_at(a, bump, 7)
    } else {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6) * spec_factor_at(a, bump, 7) * spec_factor_at(a, bump, 8)
    }
}

pub open spec fn spec_product_with_bump_at(a: Seq<i64>, bump: int) -> int
    recommends
        0 <= bump && bump < a.len(),
        a.len() <= 9,
{
    spec_prefix_with_bump(a, bump, a.len() as int)
}

pub open spec fn spec_max2(x: int, y: int) -> int {
    if x > y {
        x
    } else {
        y
    }
}

pub open spec fn spec_max_bumps_upto(a: Seq<i64>, end: int) -> int
    recommends
        0 <= end && end <= a.len() && a.len() <= 9,
{
    if end == 0 {
        0
    } else if end == 1 {
        spec_product_with_bump_at(a, 0)
    } else if end == 2 {
        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1))
    } else if end == 3 {
        spec_max2(
            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
            spec_product_with_bump_at(a, 2),
        )
    } else if end == 4 {
        spec_max2(
            spec_max2(
                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                spec_product_with_bump_at(a, 2),
            ),
            spec_product_with_bump_at(a, 3),
        )
    } else if end == 5 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                    spec_product_with_bump_at(a, 2),
                ),
                spec_product_with_bump_at(a, 3),
            ),
            spec_product_with_bump_at(a, 4),
        )
    } else if end == 6 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                        spec_product_with_bump_at(a, 2),
                    ),
                    spec_product_with_bump_at(a, 3),
                ),
                spec_product_with_bump_at(a, 4),
            ),
            spec_product_with_bump_at(a, 5),
        )
    } else if end == 7 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                            spec_product_with_bump_at(a, 2),
                        ),
                        spec_product_with_bump_at(a, 3),
                    ),
                    spec_product_with_bump_at(a, 4),
                ),
                spec_product_with_bump_at(a, 5),
            ),
            spec_product_with_bump_at(a, 6),
        )
    } else if end == 8 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                spec_product_with_bump_at(a, 2),
                            ),
                            spec_product_with_bump_at(a, 3),
                        ),
                        spec_product_with_bump_at(a, 4),
                    ),
                    spec_product_with_bump_at(a, 5),
                ),
                spec_product_with_bump_at(a, 6),
            ),
            spec_product_with_bump_at(a, 7),
        )
    } else {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                    spec_product_with_bump_at(a, 2),
                                ),
                                spec_product_with_bump_at(a, 3),
                            ),
                            spec_product_with_bump_at(a, 4),
                        ),
                        spec_product_with_bump_at(a, 5),
                    ),
                    spec_product_with_bump_at(a, 6),
                ),
                spec_product_with_bump_at(a, 7),
            ),
            spec_product_with_bump_at(a, 8),
        )
    }
}

proof fn lemma_spec_prefix_le_1e10(
    a: Seq<i64>,
    bump: int,
    until: int,
)
    requires
        0 <= until && until <= a.len(),
        a.len() <= 9,
        forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
    ensures
        spec_prefix_with_bump(a, bump, until) <= 10_000_000_000,
{
    if until == 0 {
        assert(spec_prefix_with_bump(a, bump, 0) == 1);
    } else if until == 1 {
        assert(spec_prefix_with_bump(a, bump, 1) == spec_factor_at(a, bump, 0));
        assert(spec_factor_at(a, bump, 0) <= 10);
    } else if until == 2 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        assert(spec_prefix_with_bump(a, bump, 2) == f0 * f1);
        assert(f0 <= 10 && f1 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        assert(f0 * f1 <= 10_000_000_000);
    } else if until == 3 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        assert(spec_prefix_with_bump(a, bump, 3) == f0 * f1 * f2);
        assert(f0 <= 10 && f1 <= 10 && f2 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
    } else if until == 4 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        assert(spec_prefix_with_bump(a, bump, 4) == f0 * f1 * f2 * f3);
        assert(f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
    } else if until == 5 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        let f4 = spec_factor_at(a, bump, 4);
        assert(spec_prefix_with_bump(a, bump, 5) == f0 * f1 * f2 * f3 * f4);
        assert(f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10 && f4 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3, 10_000, f4, 10);
    } else if until == 6 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        let f4 = spec_factor_at(a, bump, 4);
        let f5 = spec_factor_at(a, bump, 5);
        assert(spec_prefix_with_bump(a, bump, 6) == f0 * f1 * f2 * f3 * f4 * f5);
        assert(f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10 && f4 <= 10 && f5 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3, 10_000, f4, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4, 100_000, f5, 10);
    } else if until == 7 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        let f4 = spec_factor_at(a, bump, 4);
        let f5 = spec_factor_at(a, bump, 5);
        let f6 = spec_factor_at(a, bump, 6);
        assert(spec_prefix_with_bump(a, bump, 7) == f0 * f1 * f2 * f3 * f4 * f5 * f6);
        assert(f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10 && f4 <= 10 && f5 <= 10 && f6 <= 10);
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3, 10_000, f4, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4, 100_000, f5, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5, 1_000_000, f6, 10);
    } else if until == 8 {
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        let f4 = spec_factor_at(a, bump, 4);
        let f5 = spec_factor_at(a, bump, 5);
        let f6 = spec_factor_at(a, bump, 6);
        let f7 = spec_factor_at(a, bump, 7);
        assert(spec_prefix_with_bump(a, bump, 8) == f0 * f1 * f2 * f3 * f4 * f5 * f6 * f7);
        assert(
            f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10 && f4 <= 10 && f5 <= 10 && f6 <= 10 && f7 <= 10
        );
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3, 10_000, f4, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4, 100_000, f5, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5, 1_000_000, f6, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5 * f6, 10_000_000, f7, 10);
    } else {
        assert(until == 9);
        let f0 = spec_factor_at(a, bump, 0);
        let f1 = spec_factor_at(a, bump, 1);
        let f2 = spec_factor_at(a, bump, 2);
        let f3 = spec_factor_at(a, bump, 3);
        let f4 = spec_factor_at(a, bump, 4);
        let f5 = spec_factor_at(a, bump, 5);
        let f6 = spec_factor_at(a, bump, 6);
        let f7 = spec_factor_at(a, bump, 7);
        let f8 = spec_factor_at(a, bump, 8);
        assert(spec_prefix_with_bump(a, bump, 9) == f0 * f1 * f2 * f3 * f4 * f5 * f6 * f7 * f8);
        assert(
            f0 <= 10 && f1 <= 10 && f2 <= 10 && f3 <= 10 && f4 <= 10 && f5 <= 10 && f6 <= 10 && f7 <= 10
                && f8 <= 10
        );
        lemma_mul_upper_bound(f0, 10, f1, 10);
        lemma_mul_upper_bound(f0 * f1, 100, f2, 10);
        lemma_mul_upper_bound(f0 * f1 * f2, 1000, f3, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3, 10_000, f4, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4, 100_000, f5, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5, 1_000_000, f6, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5 * f6, 10_000_000, f7, 10);
        lemma_mul_upper_bound(f0 * f1 * f2 * f3 * f4 * f5 * f6 * f7, 100_000_000, f8, 10);
    }
}

proof fn lemma_spec_max_bumps_upto_inc(
    a: Seq<i64>,
    i: int,
)
    requires
        1 <= a.len() && a.len() <= 9,
        0 <= i && i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
    ensures
        spec_max_bumps_upto(a, i + 1)
            == spec_max2(spec_max_bumps_upto(a, i), spec_product_with_bump_at(a, i)),
{
    if i == 0 {
        assert(spec_max_bumps_upto(a, 0) == 0);
        assert(spec_max_bumps_upto(a, 1) == spec_product_with_bump_at(a, 0));
        assert(
            spec_max2(spec_max_bumps_upto(a, 0), spec_product_with_bump_at(a, 0))
                == spec_product_with_bump_at(a, 0)
        );
    } else if i == 1 {
        assert(
            spec_max_bumps_upto(a, 2)
                == spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1))
        );
        assert(spec_max_bumps_upto(a, 1) == spec_product_with_bump_at(a, 0));
        assert(
            spec_max2(spec_max_bumps_upto(a, 1), spec_product_with_bump_at(a, 1))
                == spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1))
        );
    } else if i == 2 {
        assert(
            spec_max_bumps_upto(a, 3)
                == spec_max2(
                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                    spec_product_with_bump_at(a, 2),
                )
        );
        assert(
            spec_max_bumps_upto(a, 2)
                == spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1))
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 2), spec_product_with_bump_at(a, 2))
                == spec_max2(
                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                    spec_product_with_bump_at(a, 2),
                )
        );
    } else if i == 3 {
        assert(
            spec_max_bumps_upto(a, 4)
                == spec_max2(
                    spec_max2(
                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                        spec_product_with_bump_at(a, 2),
                    ),
                    spec_product_with_bump_at(a, 3),
                )
        );
        assert(
            spec_max_bumps_upto(a, 3)
                == spec_max2(
                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                    spec_product_with_bump_at(a, 2),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 3), spec_product_with_bump_at(a, 3))
                == spec_max2(
                    spec_max2(
                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                        spec_product_with_bump_at(a, 2),
                    ),
                    spec_product_with_bump_at(a, 3),
                )
        );
    } else if i == 4 {
        assert(
            spec_max_bumps_upto(a, 5)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                            spec_product_with_bump_at(a, 2),
                        ),
                        spec_product_with_bump_at(a, 3),
                    ),
                    spec_product_with_bump_at(a, 4),
                )
        );
        assert(
            spec_max_bumps_upto(a, 4)
                == spec_max2(
                    spec_max2(
                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                        spec_product_with_bump_at(a, 2),
                    ),
                    spec_product_with_bump_at(a, 3),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 4), spec_product_with_bump_at(a, 4))
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                            spec_product_with_bump_at(a, 2),
                        ),
                        spec_product_with_bump_at(a, 3),
                    ),
                    spec_product_with_bump_at(a, 4),
                )
        );
    } else if i == 5 {
        assert(
            spec_max_bumps_upto(a, 6)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                spec_product_with_bump_at(a, 2),
                            ),
                            spec_product_with_bump_at(a, 3),
                        ),
                        spec_product_with_bump_at(a, 4),
                    ),
                    spec_product_with_bump_at(a, 5),
                )
        );
        assert(
            spec_max_bumps_upto(a, 5)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                            spec_product_with_bump_at(a, 2),
                        ),
                        spec_product_with_bump_at(a, 3),
                    ),
                    spec_product_with_bump_at(a, 4),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 5), spec_product_with_bump_at(a, 5))
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                spec_product_with_bump_at(a, 2),
                            ),
                            spec_product_with_bump_at(a, 3),
                        ),
                        spec_product_with_bump_at(a, 4),
                    ),
                    spec_product_with_bump_at(a, 5),
                )
        );
    } else if i == 6 {
        assert(
            spec_max_bumps_upto(a, 7)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                    spec_product_with_bump_at(a, 2),
                                ),
                                spec_product_with_bump_at(a, 3),
                            ),
                            spec_product_with_bump_at(a, 4),
                        ),
                        spec_product_with_bump_at(a, 5),
                    ),
                    spec_product_with_bump_at(a, 6),
                )
        );
        assert(
            spec_max_bumps_upto(a, 6)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                spec_product_with_bump_at(a, 2),
                            ),
                            spec_product_with_bump_at(a, 3),
                        ),
                        spec_product_with_bump_at(a, 4),
                    ),
                    spec_product_with_bump_at(a, 5),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 6), spec_product_with_bump_at(a, 6))
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                    spec_product_with_bump_at(a, 2),
                                ),
                                spec_product_with_bump_at(a, 3),
                            ),
                            spec_product_with_bump_at(a, 4),
                        ),
                        spec_product_with_bump_at(a, 5),
                    ),
                    spec_product_with_bump_at(a, 6),
                )
        );
    } else if i == 7 {
        assert(
            spec_max_bumps_upto(a, 8)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(
                                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                        spec_product_with_bump_at(a, 2),
                                    ),
                                    spec_product_with_bump_at(a, 3),
                                ),
                                spec_product_with_bump_at(a, 4),
                            ),
                            spec_product_with_bump_at(a, 5),
                        ),
                        spec_product_with_bump_at(a, 6),
                    ),
                    spec_product_with_bump_at(a, 7),
                )
        );
        assert(
            spec_max_bumps_upto(a, 7)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                    spec_product_with_bump_at(a, 2),
                                ),
                                spec_product_with_bump_at(a, 3),
                            ),
                            spec_product_with_bump_at(a, 4),
                        ),
                        spec_product_with_bump_at(a, 5),
                    ),
                    spec_product_with_bump_at(a, 6),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 7), spec_product_with_bump_at(a, 7))
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(
                                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                        spec_product_with_bump_at(a, 2),
                                    ),
                                    spec_product_with_bump_at(a, 3),
                                ),
                                spec_product_with_bump_at(a, 4),
                            ),
                            spec_product_with_bump_at(a, 5),
                        ),
                        spec_product_with_bump_at(a, 6),
                    ),
                    spec_product_with_bump_at(a, 7),
                )
        );
    } else {
        assert(i == 8);
        assert(
            spec_max_bumps_upto(a, 9)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(
                                        spec_max2(
                                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                            spec_product_with_bump_at(a, 2),
                                        ),
                                        spec_product_with_bump_at(a, 3),
                                    ),
                                    spec_product_with_bump_at(a, 4),
                                ),
                                spec_product_with_bump_at(a, 5),
                            ),
                            spec_product_with_bump_at(a, 6),
                        ),
                        spec_product_with_bump_at(a, 7),
                    ),
                    spec_product_with_bump_at(a, 8),
                )
        );
        assert(
            spec_max_bumps_upto(a, 8)
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(
                                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                        spec_product_with_bump_at(a, 2),
                                    ),
                                    spec_product_with_bump_at(a, 3),
                                ),
                                spec_product_with_bump_at(a, 4),
                            ),
                            spec_product_with_bump_at(a, 5),
                        ),
                        spec_product_with_bump_at(a, 6),
                    ),
                    spec_product_with_bump_at(a, 7),
                )
        );
        assert(
            spec_max2(spec_max_bumps_upto(a, 8), spec_product_with_bump_at(a, 8))
                == spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(
                                        spec_max2(
                                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                            spec_product_with_bump_at(a, 2),
                                        ),
                                        spec_product_with_bump_at(a, 3),
                                    ),
                                    spec_product_with_bump_at(a, 4),
                                ),
                                spec_product_with_bump_at(a, 5),
                            ),
                            spec_product_with_bump_at(a, 6),
                        ),
                        spec_product_with_bump_at(a, 7),
                    ),
                    spec_product_with_bump_at(a, 8),
                )
        );
    }
}

proof fn lemma_prefix_step_j(
    a: Seq<i64>,
    bump: int,
    j: int,
)
    requires
        0 <= j && j < a.len(),
        a.len() <= 9,
        forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
    ensures
        spec_prefix_with_bump(a, bump, j + 1)
            == spec_prefix_with_bump(a, bump, j) * spec_factor_at(a, bump, j),
{
    if j == 0 {
        assert(spec_prefix_with_bump(a, bump, 0) == 1);
        assert(spec_factor_at(a, bump, 0) == spec_prefix_with_bump(a, bump, 1));
    } else if j == 1 {
        assert(spec_prefix_with_bump(a, bump, 1) == spec_factor_at(a, bump, 0));
        assert(
            spec_prefix_with_bump(a, bump, 1) * spec_factor_at(a, bump, 1)
                == spec_prefix_with_bump(a, bump, 2)
        );
    } else if j == 2 {
        assert(
            spec_prefix_with_bump(a, bump, 2)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1)
        );
        assert(
            spec_prefix_with_bump(a, bump, 2) * spec_factor_at(a, bump, 2)
                == spec_prefix_with_bump(a, bump, 3)
        );
    } else if j == 3 {
        assert(
            spec_prefix_with_bump(a, bump, 3)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
        );
        assert(
            spec_prefix_with_bump(a, bump, 3) * spec_factor_at(a, bump, 3)
                == spec_prefix_with_bump(a, bump, 4)
        );
    } else if j == 4 {
        assert(
            spec_prefix_with_bump(a, bump, 4)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
                    * spec_factor_at(a, bump, 3)
        );
        assert(
            spec_prefix_with_bump(a, bump, 4) * spec_factor_at(a, bump, 4)
                == spec_prefix_with_bump(a, bump, 5)
        );
    } else if j == 5 {
        assert(
            spec_prefix_with_bump(a, bump, 5)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
                    * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4)
        );
        assert(
            spec_prefix_with_bump(a, bump, 5) * spec_factor_at(a, bump, 5)
                == spec_prefix_with_bump(a, bump, 6)
        );
    } else if j == 6 {
        assert(
            spec_prefix_with_bump(a, bump, 6)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
                    * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
        );
        assert(
            spec_prefix_with_bump(a, bump, 6) * spec_factor_at(a, bump, 6)
                == spec_prefix_with_bump(a, bump, 7)
        );
    } else if j == 7 {
        assert(
            spec_prefix_with_bump(a, bump, 7)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
                    * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
                    * spec_factor_at(a, bump, 6)
        );
        assert(
            spec_prefix_with_bump(a, bump, 7) * spec_factor_at(a, bump, 7)
                == spec_prefix_with_bump(a, bump, 8)
        );
    } else {
        assert(j == 8);
        assert(
            spec_prefix_with_bump(a, bump, 8)
                == spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
                    * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
                    * spec_factor_at(a, bump, 6) * spec_factor_at(a, bump, 7)
        );
        assert(
            spec_prefix_with_bump(a, bump, 8) * spec_factor_at(a, bump, 8)
                == spec_prefix_with_bump(a, bump, 9)
        );
    }
    assert(spec_prefix_with_bump(a, bump, j + 1)
        == spec_prefix_with_bump(a, bump, j) * spec_factor_at(a, bump, j));
}

impl Solution {
    pub fn max_product_one_increment(a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() && a.len() <= 9,
            forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
        ensures
            res as int == spec_max_bumps_upto(a@, a.len() as int),
    {
        let n = a.len();
        let mut best: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                1 <= n && n <= 9,
                forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
                i <= n,
                (best as int) == spec_max_bumps_upto(a@, i as int),
                best <= 10_000_000_000,
            decreases n - i,
        {
            let mut p: i64 = 1;
            let mut j: usize = 0;
            while j < n
                invariant
                    n == a.len(),
                    a.len() <= 9,
                    i < n,
                    j <= n,
                    forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
                    (p as int) == spec_prefix_with_bump(a@, i as int, j as int),
                    p >= 0,
                    p <= 10_000_000_000,
                decreases n - j,
            {
                proof {
                    lemma_prefix_step_j(a@, i as int, j as int);
                    lemma_spec_prefix_le_1e10(a@, i as int, j as int);
                    assert((p as int) <= 10_000_000_000);
                    assert((a@[j as int] as int) <= 9);
                    assert((a@[j as int] + 1) as int <= 10);
                    assert(spec_factor_at(a@, i as int, j as int) <= 10);
                    lemma_mul_upper_bound(
                        (p as int),
                        10_000_000_000,
                        spec_factor_at(a@, i as int, j as int),
                        10,
                    );
                }
                if j == i {
                    p = p * (a[j] + 1);
                } else {
                    p = p * a[j];
                }
                proof {
                    assert((p as int) == spec_prefix_with_bump(a@, i as int, j as int + 1));
                }
                j = j + 1;
                proof {
                    assert((p as int) == spec_prefix_with_bump(a@, i as int, j as int));
                    lemma_spec_prefix_le_1e10(a@, i as int, j as int);
                }
            }
            proof {
                assert((p as int) == spec_product_with_bump_at(a@, i as int));
                lemma_spec_max_bumps_upto_inc(a@, i as int);
            }
            let ghost old_best = best;
            if p > best {
                best = p;
            }
            proof {
                assert((best as int) == spec_max2(old_best as int, (p as int)));
                assert((old_best as int) == spec_max_bumps_upto(a@, i as int));
                assert((best as int) == spec_max_bumps_upto(a@, (i + 1) as int));
            }
            i = i + 1;
        }
        proof {
            assert((best as int) == spec_max_bumps_upto(a@, n as int));
        }
        best
    }
}

}
