use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    pub open spec fn dp_rec_mod(kind: int, len: int, v: int, cost: int, modv: int) -> int
        decreases len, v, kind
    {
        if kind == 0 {
            if len <= 0 || v <= 0 || cost <= 0 { 0 }
            else if len == 1 {
                if cost == 1 { 1 } else { 0 }
            } else {
                ((v * Self::dp_rec_mod(0, len - 1, v, cost, modv)) % modv
                    + Self::dp_rec_mod(1, len - 1, v - 1, cost - 1, modv)) % modv
            }
        } else if kind == 1 {
            if v <= 0 || len <= 0 || cost <= 0 { 0 }
            else {
                (Self::dp_rec_mod(1, len, v - 1, cost, modv)
                    + Self::dp_rec_mod(0, len, v, cost, modv)) % modv
            }
        } else {
            0
        }
    }

    
    pub open spec fn dp_val_mod(len: int, v: int, cost: int, modv: int) -> int {
        Self::dp_rec_mod(0, len, v, cost, modv)
    }

    
    pub open spec fn prefix_val_mod(len: int, v: int, cost: int, modv: int) -> int {
        Self::dp_rec_mod(1, len, v, cost, modv)
    }

    proof fn dp_rec_mod_bounds(kind: int, len: int, v: int, cost: int, modv: int)
        requires
            modv > 1,
        ensures
            0 <= Self::dp_rec_mod(kind, len, v, cost, modv) < modv,
        decreases len, v, kind
    {
        if kind == 0 {
            if len <= 0 || v <= 0 || cost <= 0 {
            } else if len == 1 {
            } else {
                Self::dp_rec_mod_bounds(0, len - 1, v, cost, modv);
                Self::dp_rec_mod_bounds(1, len - 1, v - 1, cost - 1, modv);
            }
        } else if kind == 1 {
            if v <= 0 || len <= 0 || cost <= 0 {
            } else {
                Self::dp_rec_mod_bounds(1, len, v - 1, cost, modv);
                Self::dp_rec_mod_bounds(0, len, v, cost, modv);
            }
        } else {
        }
    }

    proof fn base_dp_val(v: int, cost: int, modv: int)
        requires
            v >= 1,
            modv > 1,
        ensures
            Self::dp_val_mod(1, v, cost, modv) == if cost == 1 { 1int } else { 0int },
    {
    }

    proof fn base_prefix_val(v: int, cost: int, modv: int)
        requires
            v >= 1,
            cost >= 1,
            modv > v,
        ensures
            Self::prefix_val_mod(1, v, cost, modv) == if cost == 1 { v } else { 0int },
        decreases v
    {
        Self::base_dp_val(v, cost, modv);
        Self::dp_rec_mod_bounds(0, 1, v, cost, modv);
        if v == 1 {
            assert(Self::dp_rec_mod(1, 1, 0, cost, modv) == 0);
            if cost == 1 {
                assert(1int % modv == 1int) by(nonlinear_arith)
                    requires modv > 1;
            } else {
                assert(0int % modv == 0int) by(nonlinear_arith)
                    requires modv > 1;
            }
        } else {
            Self::base_prefix_val(v - 1, cost, modv);
            Self::dp_rec_mod_bounds(1, 1, v - 1, cost, modv);
            if cost == 1 {
                assert(Self::dp_rec_mod(1, 1, v - 1, 1, modv) == v - 1);
                assert(Self::dp_rec_mod(0, 1, v, 1, modv) == 1);
                assert(v % modv == v) by(nonlinear_arith)
                    requires 0 < v, v < modv;
            } else {
                assert(Self::dp_rec_mod(1, 1, v - 1, cost, modv) == 0);
                assert(Self::dp_rec_mod(0, 1, v, cost, modv) == 0);
                assert(0int % modv == 0int) by(nonlinear_arith)
                    requires modv > 1;
            }
        }
    }

    proof fn prefix_zero_v(len: int, cost: int, modv: int)
        ensures
            Self::prefix_val_mod(len, 0, cost, modv) == 0,
    {
    }

    proof fn prefix_val_zero_cost(len: int, v: int, modv: int)
        requires
            modv > 1,
        ensures
            Self::prefix_val_mod(len, v, 0, modv) == 0,
        decreases v
    {
        if v <= 0 {
        } else {
            Self::prefix_val_zero_cost(len, v - 1, modv);
        }
    }

    proof fn col0_in_bounds(jj: int, stride: int, mi: int, ki: int, sz: int)
        requires 1 <= jj <= mi, stride == ki + 1, sz == (mi + 1) * stride, ki >= 1,
        ensures 0 <= jj * stride, jj * stride < sz,
    {
        assert(jj * stride >= 0) by(nonlinear_arith) requires jj >= 1, stride >= 1;
        assert(jj * stride < sz) by(nonlinear_arith)
            requires jj <= mi, stride == ki + 1, sz == (mi + 1) * stride, ki >= 1;
    }


    proof fn row0_ne_set(c: int, mn: int, stride: int, cost: int)
        requires 0 <= c < stride, mn >= 1, stride >= 2, cost >= 1,
        ensures c != mn * stride + cost,
    {
        assert(c < mn * stride + cost) by(nonlinear_arith)
            requires 0 <= c < stride, mn >= 1, stride >= 2, cost >= 1;
    }

    fn create_zero_vec(sz: usize) -> (v: Vec<i64>)
        requires
            sz <= 5200,
        ensures
            v.len() == sz,
            forall |i: int| 0 <= i < sz as int ==> #[trigger] v@[i] == 0i64,
    {
        let mut v: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < sz
            invariant
                j <= sz,
                sz <= 5200,
                v.len() == j as int,
                forall |i: int| 0 <= i < j as int ==> #[trigger] v@[i] == 0i64,
            decreases sz - j,
        {
            v.push(0i64);
            j = j + 1;
        }
        v
    }

    pub fn num_of_arrays(n: i32, m: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 50,
            1 <= m <= 100,
            0 <= k <= n,
        ensures
            0 <= result < 1_000_000_007,
            result == Self::prefix_val_mod(n as int, m as int, k as int, 1_000_000_007) as i32,
    {
        let modv: i64 = 1_000_000_007;
        let ni = n as usize;
        let mi = m as usize;
        let ki = k as usize;
        let stride: usize = ki + 1;
        assert((mi + 1) * (ki + 1) <= 101 * 51) by(nonlinear_arith)
            requires mi <= 100, ki <= 50;
        let sz: usize = (mi + 1) * stride;

        assert(sz <= 5151) by(nonlinear_arith)
            requires mi <= 100, ki <= 50, stride == ki + 1, sz == (mi + 1) * stride;

        if ki == 0 {
            proof {
                Self::prefix_val_zero_cost(n as int, m as int, modv as int);
                Self::dp_rec_mod_bounds(1, n as int, m as int, 0, modv as int);
            }
            return 0i32;
        }

        let mut prev_dp = Self::create_zero_vec(sz);
        let mut prev_prefix = Self::create_zero_vec(sz);

        proof {
            assert forall |jj: int, c: int|
                1 <= jj <= mi as int && 0 <= c <= ki as int
            implies
                (#[trigger] prev_dp@[jj * (stride as int) + c]) == 0i64
            by {
                assert(0 <= jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                    requires 1 <= jj <= mi as int, 0 <= c <= ki as int,
                        stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
            }
            assert forall |jj: int, c: int|
                1 <= jj <= mi as int && 0 <= c <= ki as int
            implies
                (#[trigger] prev_prefix@[jj * (stride as int) + c]) == 0i64
            by {
                assert(0 <= jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                    requires 1 <= jj <= mi as int, 0 <= c <= ki as int,
                        stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
            }
            assert forall |c: int| 0 <= c <= ki as int
            implies (#[trigger] prev_dp@[c]) == 0i64
            by {
                assert(0 <= c < sz as int) by(nonlinear_arith)
                    requires 0 <= c <= ki as int, stride == ki as int + 1,
                        sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
            }
            assert forall |c: int| 0 <= c <= ki as int
            implies (#[trigger] prev_prefix@[c]) == 0i64
            by {
                assert(0 <= c < sz as int) by(nonlinear_arith)
                    requires 0 <= c <= ki as int, stride == ki as int + 1,
                        sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
            }
        }

        proof {
            assert forall |jj: int| 1 <= jj <= mi as int
            implies 0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int
            by {
                Self::col0_in_bounds(jj, stride as int, mi as int, ki as int, sz as int);
            }
            assert((ki as int) < (sz as int)) by(nonlinear_arith)
                requires mi as int >= 1, ki as int >= 1,
                    stride == ki as int + 1, sz == (mi as int + 1) * stride;
        }

        let mut j: usize = 1;
        while j <= mi
            invariant
                1 <= j <= mi + 1,
                prev_dp.len() == sz,
                prev_prefix.len() == sz,
                sz == (mi + 1) * stride,
                stride == ki + 1,
                mi == m as usize,
                ki == k as usize,
                mi <= 100,
                ki <= 50,
                ki >= 1,
                modv == 1_000_000_007i64,
                1 <= m <= 100,
                0 <= k <= n,
                1 <= n <= 50,
                sz <= 5151,
                forall |jj: int| 1 <= jj <= mi as int ==>
                    0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int,
                (ki as int) < (sz as int),
                forall |jj: int, c: int|
                    1 <= jj < j as int && 1 <= c <= ki as int ==>
                    (#[trigger] prev_dp@[jj * (stride as int) + c])
                        == Self::dp_val_mod(1, jj, c, modv as int) as i64,
                forall |jj: int, c: int|
                    1 <= jj < j as int && 1 <= c <= ki as int ==>
                    (#[trigger] prev_prefix@[jj * (stride as int) + c])
                        == Self::prefix_val_mod(1, jj, c, modv as int) as i64,
                forall |jj: int, c: int|
                    j as int <= jj <= mi as int && 0 <= c <= ki as int ==>
                    (#[trigger] prev_dp@[jj * (stride as int) + c]) == 0i64,
                forall |jj: int, c: int|
                    j as int <= jj <= mi as int && 0 <= c <= ki as int ==>
                    (#[trigger] prev_prefix@[jj * (stride as int) + c]) == 0i64,
                forall |c: int| 0 <= c <= ki as int ==>
                    (#[trigger] prev_dp@[c]) == 0i64,
                forall |c: int| 0 <= c <= ki as int ==>
                    (#[trigger] prev_prefix@[c]) == 0i64,
                forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_dp@[i],
                forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_prefix@[i],
                forall |i: int| 0 <= i < sz as int ==> #[trigger] prev_dp@[i] < modv,
                forall |i: int| 0 <= i < sz as int ==> #[trigger] prev_prefix@[i] < modv,
            decreases mi + 1 - j,
        {
            assert(j * stride + 1 < sz) by(nonlinear_arith)
                requires 1 <= j <= mi, mi <= 100, stride == ki + 1, ki >= 1, ki <= 50, sz == (mi + 1) * stride;

            proof {
                assert forall |jj: int, c: int|
                    1 <= jj <= mi as int && 0 <= c <= ki as int
                implies 0 <= #[trigger] (jj * (stride as int) + c) && (jj * (stride as int) + c) < sz as int
                by {
                    assert(0 <= jj * (stride as int) + c) by(nonlinear_arith)
                        requires jj >= 1, stride >= 1, c >= 0;
                    assert(jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                        requires jj <= mi as int, c <= ki as int,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride;
                }
            }

            proof {
                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] prev_dp@[(j as int) * (stride as int) + c]) == 0i64
                by {
                    assert(0 <= (j as int) * (stride as int) + c < sz as int) by(nonlinear_arith)
                        requires 1 <= j as int <= mi as int, 0 <= c <= ki as int,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] prev_prefix@[(j as int) * (stride as int) + c]) == 0i64
                by {
                    assert(0 <= (j as int) * (stride as int) + c < sz as int) by(nonlinear_arith)
                        requires 1 <= j as int <= mi as int, 0 <= c <= ki as int,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
            }

            prev_dp.set(j * stride + 1, 1i64);


            prev_prefix.set(j * stride + 1, j as i64);

            proof {
                Self::base_dp_val(j as int, 1, modv as int);
                Self::base_prefix_val(j as int, 1, modv as int);

                assert((j * stride + 1) as int == (j as int) * (stride as int) + 1);

                assert forall |jj: int, c: int|
                    1 <= jj < (j + 1) as int && 1 <= c <= ki as int
                implies
                    (#[trigger] prev_dp@[jj * (stride as int) + c])
                        == Self::dp_val_mod(1, jj, c, modv as int) as i64
                by {
                    if jj == j as int {
                        if c != 1 {
                            assert(jj * (stride as int) + c != (j as int) * (stride as int) + 1);
                        }
                        Self::base_dp_val(jj, c, modv as int);
                        Self::dp_rec_mod_bounds(0, 1, jj, c, modv as int);
                    } else {
                        assert(jj * (stride as int) + c < (j as int) * (stride as int)) by(nonlinear_arith)
                            requires jj < j as int, c <= ki as int, stride == ki as int + 1, ki >= 1;
                    }
                }

                assert forall |jj: int, c: int|
                    1 <= jj < (j + 1) as int && 1 <= c <= ki as int
                implies
                    (#[trigger] prev_prefix@[jj * (stride as int) + c])
                        == Self::prefix_val_mod(1, jj, c, modv as int) as i64
                by {
                    if jj == j as int {
                        if c != 1 {
                            assert(jj * (stride as int) + c != (j as int) * (stride as int) + 1);
                        }
                        Self::base_prefix_val(jj, c, modv as int);
                        Self::dp_rec_mod_bounds(1, 1, jj, c, modv as int);
                    } else {
                        assert(jj * (stride as int) + c < (j as int) * (stride as int)) by(nonlinear_arith)
                            requires jj < j as int, c <= ki as int, stride == ki as int + 1, ki >= 1;
                    }
                }

                assert forall |jj: int, c: int|
                    (j + 1) as int <= jj <= mi as int && 0 <= c <= ki as int
                implies
                    (#[trigger] prev_dp@[jj * (stride as int) + c]) == 0i64
                by {
                    assert(jj * (stride as int) + c > (j as int) * (stride as int) + 1) by(nonlinear_arith)
                        requires jj >= (j as int) + 1, stride >= 2, c >= 0, stride == ki as int + 1;
                }

                assert forall |jj: int, c: int|
                    (j + 1) as int <= jj <= mi as int && 0 <= c <= ki as int
                implies
                    (#[trigger] prev_prefix@[jj * (stride as int) + c]) == 0i64
                by {
                    assert(jj * (stride as int) + c > (j as int) * (stride as int) + 1) by(nonlinear_arith)
                        requires jj >= (j as int) + 1, stride >= 2, c >= 0, stride == ki as int + 1;
                }

                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] prev_dp@[c]) == 0i64
                by {
                    assert(c < (j as int) * (stride as int) + 1) by(nonlinear_arith)
                        requires c <= ki as int, stride == ki as int + 1, j >= 1;
                }
                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] prev_prefix@[c]) == 0i64
                by {
                    assert(c < (j as int) * (stride as int) + 1) by(nonlinear_arith)
                        requires c <= ki as int, stride == ki as int + 1, j >= 1;
                }

            }

            j = j + 1;
        }

        let mut len: usize = 2;
        while len <= ni
            invariant
                2 <= len <= ni + 1,
                ni == n as usize,
                mi == m as usize,
                ki == k as usize,
                stride == ki + 1,
                sz == (mi + 1) * stride,
                modv == 1_000_000_007i64,
                1 <= n <= 50,
                1 <= m <= 100,
                0 <= k <= n,
                mi <= 100,
                ki <= 50,
                ki >= 1,
                sz <= 5151,
                prev_dp.len() == sz,
                prev_prefix.len() == sz,
                forall |jj: int, c: int|
                    1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                    (#[trigger] prev_dp@[jj * (stride as int) + c])
                        == Self::dp_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                forall |jj: int, c: int|
                    1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                    (#[trigger] prev_prefix@[jj * (stride as int) + c])
                        == Self::prefix_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_dp@[i] < modv,
                forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_prefix@[i] < modv,
            decreases ni + 1 - len,
        {
            let mut dp = Self::create_zero_vec(sz);
            let mut prefix = Self::create_zero_vec(sz);
            let mut max_num: usize = 1;

            proof {
                assert forall |jj: int, c: int|
                    1 <= jj <= mi as int && 0 <= c <= ki as int
                implies
                    (#[trigger] dp@[jj * (stride as int) + c]) == 0i64
                by {
                    assert(0 <= jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                        requires 1 <= jj <= mi as int, 0 <= c <= ki as int,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
                assert forall |jj: int, c: int|
                    1 <= jj <= mi as int && 0 <= c <= ki as int
                implies
                    (#[trigger] prefix@[jj * (stride as int) + c]) == 0i64
                by {
                    assert(0 <= jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                        requires 1 <= jj <= mi as int, 0 <= c <= ki as int,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] dp@[c]) == 0i64
                by {
                    assert(0 <= c < sz as int) by(nonlinear_arith)
                        requires 0 <= c <= ki as int, stride == ki as int + 1,
                            sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
                assert forall |c: int| 0 <= c <= ki as int
                implies (#[trigger] prefix@[c]) == 0i64
                by {
                    assert(0 <= c < sz as int) by(nonlinear_arith)
                        requires 0 <= c <= ki as int, stride == ki as int + 1,
                            sz == (mi as int + 1) * stride, mi >= 1, ki >= 1;
                }
            }
            proof {
                assert forall |jj: int| 1 <= jj <= mi as int
                implies 0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int
                by {
                    Self::col0_in_bounds(jj, stride as int, mi as int, ki as int, sz as int);
                }
                assert((ki as int) < (sz as int)) by(nonlinear_arith)
                    requires mi as int >= 1, ki as int >= 1,
                        stride == ki as int + 1, sz == (mi as int + 1) * stride;
            }
            while max_num <= mi
                invariant
                    1 <= max_num <= mi + 1,
                    dp.len() == sz,
                    prefix.len() == sz,
                    prev_dp.len() == sz,
                    prev_prefix.len() == sz,
                    sz == (mi + 1) * stride,
                    stride == ki + 1,
                    mi == m as usize,
                    ki == k as usize,
                    modv == 1_000_000_007i64,
                    2 <= len <= ni,
                    ni == n as usize,
                    1 <= n <= 50,
                    1 <= m <= 100,
                    0 <= k <= n,
                    mi <= 100,
                    ki <= 50,
                    ki >= 1,
                    sz <= 5151,
                    forall |jj: int| 1 <= jj <= mi as int ==>
                        0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int,
                    (ki as int) < (sz as int),
                    forall |jj: int, c: int|
                        1 <= jj < max_num as int && 1 <= c <= ki as int ==>
                        (#[trigger] dp@[jj * (stride as int) + c])
                            == Self::dp_val_mod(len as int, jj, c, modv as int) as i64,
                    forall |jj: int, c: int|
                        1 <= jj < max_num as int && 1 <= c <= ki as int ==>
                        (#[trigger] prefix@[jj * (stride as int) + c])
                            == Self::prefix_val_mod(len as int, jj, c, modv as int) as i64,
                    forall |jj: int, c: int|
                        max_num as int <= jj <= mi as int && 0 <= c <= ki as int ==>
                        (#[trigger] dp@[jj * (stride as int) + c]) == 0i64,
                    forall |jj: int, c: int|
                        max_num as int <= jj <= mi as int && 0 <= c <= ki as int ==>
                        (#[trigger] prefix@[jj * (stride as int) + c]) == 0i64,
                    forall |c: int|
                        0 <= c <= ki as int ==>
                        (#[trigger] dp@[c]) == 0i64,
                    forall |c: int|
                        0 <= c <= ki as int ==>
                        (#[trigger] prefix@[c]) == 0i64,
                    forall |jj: int, c: int|
                        1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                        (#[trigger] prev_dp@[jj * (stride as int) + c])
                            == Self::dp_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                    forall |jj: int, c: int|
                        1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                        (#[trigger] prev_prefix@[jj * (stride as int) + c])
                            == Self::prefix_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                    forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_dp@[i] < modv,
                    forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_prefix@[i] < modv,
                    forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] dp@[i] < modv,
                    forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prefix@[i] < modv,
                decreases mi + 1 - max_num,
            {
                proof {
                    assert forall |jj: int, c: int|
                        1 <= jj <= mi as int && 0 <= c <= ki as int
                    implies 0 <= #[trigger] (jj * (stride as int) + c) && (jj * (stride as int) + c) < sz as int
                    by {
                        assert(0 <= jj * (stride as int) + c) by(nonlinear_arith)
                            requires jj >= 1, stride >= 1, c >= 0;
                        assert(jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                            requires jj <= mi as int, c <= ki as int,
                                stride == ki as int + 1, sz == (mi as int + 1) * stride;
                    }

                    assert((ki as int) < (sz as int)) by(nonlinear_arith)
                        requires mi as int >= 1, ki as int >= 1,
                            stride == ki as int + 1, sz == (mi as int + 1) * stride;
                    assert(dp@.len() == sz as int);
                    assert(prefix@.len() == sz as int);

                    assert forall |jj: int| 1 <= jj <= mi as int
                    implies 0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int
                    by {
                        Self::col0_in_bounds(jj, stride as int, mi as int, ki as int, sz as int);
                    }

                }
                let mut cost: usize = 1;
                while cost <= ki
                    invariant
                        1 <= cost <= ki + 1,
                        1 <= max_num <= mi,
                        dp.len() == sz,
                        prefix.len() == sz,
                        prev_dp.len() == sz,
                        prev_prefix.len() == sz,
                        sz == (mi + 1) * stride,
                        stride == ki + 1,
                        mi == m as usize,
                        ki == k as usize,
                        modv == 1_000_000_007i64,
                        2 <= len <= ni,
                        ni == n as usize,
                        1 <= n <= 50,
                        1 <= m <= 100,
                        0 <= k <= n,
                        mi <= 100,
                        ki <= 50,
                        ki >= 1,
                        sz <= 5151,
                        forall |c: int|
                            1 <= c < cost as int ==>
                            (#[trigger] dp@[(max_num as int) * (stride as int) + c])
                                == Self::dp_val_mod(len as int, max_num as int, c, modv as int) as i64,
                        forall |c: int|
                            1 <= c < cost as int ==>
                            (#[trigger] prefix@[(max_num as int) * (stride as int) + c])
                                == Self::prefix_val_mod(len as int, max_num as int, c, modv as int) as i64,
                        forall |c: int|
                            cost as int <= c <= ki as int ==>
                            (#[trigger] dp@[(max_num as int) * (stride as int) + c]) == 0i64,
                        forall |c: int|
                            cost as int <= c <= ki as int ==>
                            (#[trigger] prefix@[(max_num as int) * (stride as int) + c]) == 0i64,
                        forall |jj: int, c: int|
                            1 <= jj < max_num as int && 1 <= c <= ki as int ==>
                            (#[trigger] dp@[jj * (stride as int) + c])
                                == Self::dp_val_mod(len as int, jj, c, modv as int) as i64,
                        forall |jj: int, c: int|
                            1 <= jj < max_num as int && 1 <= c <= ki as int ==>
                            (#[trigger] prefix@[jj * (stride as int) + c])
                                == Self::prefix_val_mod(len as int, jj, c, modv as int) as i64,
                        forall |jj: int, c: int|
                            (max_num as int + 1) <= jj <= mi as int && 0 <= c <= ki as int ==>
                            (#[trigger] dp@[jj * (stride as int) + c]) == 0i64,
                        forall |jj: int, c: int|
                            (max_num as int + 1) <= jj <= mi as int && 0 <= c <= ki as int ==>
                            (#[trigger] prefix@[jj * (stride as int) + c]) == 0i64,
                        forall |c: int|
                            0 <= c <= ki as int ==>
                            (#[trigger] dp@[c]) == 0i64,
                        forall |c: int|
                            0 <= c <= ki as int ==>
                            (#[trigger] prefix@[c]) == 0i64,
                        forall |jj: int, c: int|
                            1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                            (#[trigger] prev_dp@[jj * (stride as int) + c])
                                == Self::dp_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                        forall |jj: int, c: int|
                            1 <= jj <= mi as int && 1 <= c <= ki as int ==>
                            (#[trigger] prev_prefix@[jj * (stride as int) + c])
                                == Self::prefix_val_mod((len - 1) as int, jj, c, modv as int) as i64,
                        forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_dp@[i] < modv,
                        forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prev_prefix@[i] < modv,
                        forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] dp@[i] < modv,
                        forall |i: int| 0 <= i < sz as int ==> 0 <= #[trigger] prefix@[i] < modv,
                        forall |jj: int| 1 <= jj <= mi as int ==>
                            0 <= #[trigger] (jj * (stride as int)) && (jj * (stride as int)) < sz as int,
                        (ki as int) < (sz as int),
                    decreases ki + 1 - cost,
                {
                    proof {
                        assert forall |jj: int, c: int|
                            1 <= jj <= mi as int && 0 <= c <= ki as int
                        implies 0 <= #[trigger] (jj * (stride as int) + c) && (jj * (stride as int) + c) < sz as int
                        by {
                            assert(0 <= jj * (stride as int) + c) by(nonlinear_arith)
                                requires jj >= 1, stride >= 1, c >= 0;
                            assert(jj * (stride as int) + c < sz as int) by(nonlinear_arith)
                                requires jj <= mi as int, c <= ki as int,
                                    stride == ki as int + 1, sz == (mi as int + 1) * stride;
                        }

                        assert((max_num as int) * (stride as int) + (cost as int) <= 5150) by(nonlinear_arith)
                            requires max_num as int <= 100, stride as int <= 51, cost as int <= 50;
                        assert((max_num as int) * (stride as int) + (cost as int) < sz as int) by(nonlinear_arith)
                            requires 1 <= max_num as int <= mi as int, 1 <= cost as int <= ki as int,
                                stride == ki as int + 1, sz == (mi as int + 1) * stride;
                        assert(((max_num as int) - 1) * (stride as int) + (cost as int) < sz as int) by(nonlinear_arith)
                            requires max_num as int >= 1, max_num as int <= mi as int, cost as int <= ki as int,
                                stride == ki as int + 1, sz == (mi as int + 1) * stride;
                    }

                    let cur = max_num * stride + cost;

                    proof {
                        assert(0 <= cur as int);
                        assert(cur < sz);
                        assert(0 <= prev_dp@[cur as int] < modv);
                        assert((max_num as i64) >= 0i64);
                        assert(prev_dp@[cur as int] >= 0i64);
                        assert((max_num as i64) * prev_dp@[cur as int] <= 100 * (modv - 1)) by(nonlinear_arith)
                            requires (max_num as i64) <= 100, prev_dp@[cur as int] < modv,
                                prev_dp@[cur as int] >= 0, (max_num as i64) >= 0, modv == 1_000_000_007;
                    }

                    let dp_term = (max_num as i64 * prev_dp[cur]) % modv;

                    proof {
                        if max_num > 1 && cost > 1 {
                            assert(((max_num as int) - 1) * (stride as int) + ((cost as int) - 1) < sz as int) by(nonlinear_arith)
                                requires max_num as int >= 2, max_num as int <= mi as int, cost as int >= 2, cost as int <= ki as int,
                                    stride == ki as int + 1, sz == (mi as int + 1) * stride;
                        }
                    }

                    let prefix_term: i64 = if max_num > 1 && cost > 1 {
                        prev_prefix[(max_num - 1) * stride + (cost - 1)]
                    } else {
                        0i64
                    };

                    proof {
                        assert(0 <= dp_term < modv);
                        assert(0 <= prefix_term < modv);
                        assert(dp_term + prefix_term < 2 * modv) by(nonlinear_arith)
                            requires 0 <= dp_term < modv, 0 <= prefix_term < modv;
                    }

                    let new_dp_val = (dp_term + prefix_term) % modv;

                    proof {
                        assert forall |cc: int| (cost as int) <= cc <= ki as int
                        implies (#[trigger] dp@[(max_num as int) * (stride as int) + cc]) == 0i64
                        by {}
                        assert forall |cc: int| (cost as int) <= cc <= ki as int
                        implies (#[trigger] prefix@[(max_num as int) * (stride as int) + cc]) == 0i64
                        by {}
                    }

                    let ghost snap_prefix_row0 = prefix@;
                    proof {
                        assert(snap_prefix_row0.len() == sz as int);
                        assert forall |cc: int| 0 <= cc <= ki as int
                        implies (#[trigger] snap_prefix_row0[cc]) == 0i64
                        by {
                            assert(cc <= ki as int);
                            assert((ki as int) < (sz as int));
                            assert(cc < sz as int);
                            assert(cc < snap_prefix_row0.len());
                            assert(prefix@[cc] == 0i64);
                        }
                    }

                    dp.set(cur, new_dp_val);

                    proof {
                        assert(cur as int == (max_num as int) * (stride as int) + (cost as int));
                        assert(((max_num as int) - 1) * (stride as int) + (cost as int) < sz as int);
                        assert(((max_num as int) - 1) * (stride as int) + (cost as int) !=
                               (max_num as int) * (stride as int) + (cost as int)) by(nonlinear_arith)
                            requires max_num as int >= 1, stride >= 2;
                        assert(0 <= prefix@[((max_num - 1) as int) * (stride as int) + (cost as int)] < modv);
                        assert(0 <= new_dp_val < modv);
                        assert(prefix@[((max_num - 1) as int) * (stride as int) + (cost as int)] + new_dp_val < 2 * modv) by(nonlinear_arith)
                            requires 0 <= prefix@[((max_num - 1) as int) * (stride as int) + (cost as int)] < modv, 0 <= new_dp_val < modv;
                    }

                    let new_prefix_val = (prefix[(max_num - 1) * stride + cost] + new_dp_val) % modv;
                    prefix.set(max_num * stride + cost, new_prefix_val);

                    proof {
                        let mn = max_num as int;
                        let c = cost as int;
                        let s = stride as int;
                        let l = len as int;
                        let mv = modv as int;

                        assert(cur as int == mn * s + c);
                        assert((max_num * stride + cost) as int == mn * s + c);

                        Self::dp_rec_mod_bounds(0, l - 1, mn, c, mv);
                        Self::dp_rec_mod_bounds(1, l - 1, mn - 1, c - 1, mv);

                        assert(prev_dp@[mn * s + c]
                            == Self::dp_val_mod(l - 1, mn, c, mv) as i64);

                        if mn > 1 && c > 1 {
                            assert(prev_prefix@[(mn - 1) * s + (c - 1)]
                                == Self::prefix_val_mod(l - 1, mn - 1, c - 1, mv) as i64);
                            assert(prefix_term as int
                                == Self::prefix_val_mod(l - 1, mn - 1, c - 1, mv));
                        } else {
                            if mn <= 1 {
                                Self::prefix_zero_v(l - 1, c - 1, mv);
                            } else {
                                Self::prefix_val_zero_cost(l - 1, mn - 1, mv);
                            }
                            assert(Self::dp_rec_mod(1, l - 1, mn - 1, c - 1, mv) == 0);
                            assert(prefix_term == 0i64);
                        }

                        assert(new_dp_val as int
                            == ((mn * Self::dp_rec_mod(0, l - 1, mn, c, mv)) % mv
                                + Self::dp_rec_mod(1, l - 1, mn - 1, c - 1, mv)) % mv);
                        assert(new_dp_val as int == Self::dp_rec_mod(0, l, mn, c, mv));
                        assert(new_dp_val as int == Self::dp_val_mod(l, mn, c, mv));
                        Self::dp_rec_mod_bounds(0, l, mn, c, mv);

                        assert(dp@[mn * s + c] == Self::dp_val_mod(l, mn, c, mv) as i64);

                        if mn == 1 {
                            Self::prefix_zero_v(l, c, mv);
                            assert(cur as int == mn * s + c);
                            assert((max_num * stride + cost) as int == mn * s + c);
                            assert(mn * s + c != c) by(nonlinear_arith)
                                requires mn >= 1, s >= 2;
                            assert((max_num * stride + cost) as int != c);
                            assert(c != cur as int);
                            assert(snap_prefix_row0[c] == 0i64);
                            assert(prefix@[c] == 0i64);
                            assert(Self::prefix_val_mod(l, 0, c, mv) == 0);
                        } else {
                            assert((mn - 1) * s + c != mn * s + c) by(nonlinear_arith)
                                requires mn >= 2, s >= 2;
                            assert(prefix@[(mn - 1) * s + c]
                                == Self::prefix_val_mod(l, mn - 1, c, mv) as i64);
                        }

                        Self::dp_rec_mod_bounds(1, l, mn - 1, c, mv);
                        Self::dp_rec_mod_bounds(0, l, mn, c, mv);

                        assert(new_prefix_val as int
                            == (Self::prefix_val_mod(l, mn - 1, c, mv)
                                + Self::dp_val_mod(l, mn, c, mv)) % mv);
                        assert(new_prefix_val as int
                            == (Self::dp_rec_mod(1, l, mn - 1, c, mv)
                                + Self::dp_rec_mod(0, l, mn, c, mv)) % mv);
                        assert(new_prefix_val as int == Self::dp_rec_mod(1, l, mn, c, mv));
                        assert(new_prefix_val as int == Self::prefix_val_mod(l, mn, c, mv));
                        Self::dp_rec_mod_bounds(1, l, mn, c, mv);
                        assert(prefix@[mn * s + c] == Self::prefix_val_mod(l, mn, c, mv) as i64);

                        assert forall |cc: int|
                            1 <= cc < (c + 1)
                        implies
                            (#[trigger] dp@[(max_num as int) * (stride as int) + cc])
                                == Self::dp_val_mod(l, mn, cc, mv) as i64
                        by {}

                        assert forall |cc: int|
                            1 <= cc < (c + 1)
                        implies
                            (#[trigger] prefix@[(max_num as int) * (stride as int) + cc])
                                == Self::prefix_val_mod(l, mn, cc, mv) as i64
                        by {}

                        assert forall |cc: int|
                            (c + 1) <= cc <= ki as int
                        implies
                            (#[trigger] dp@[(max_num as int) * (stride as int) + cc]) == 0i64
                        by {
                            assert(0 <= mn * s + cc < sz as int) by(nonlinear_arith)
                                requires 1 <= mn <= mi as int, 0 <= cc <= ki as int,
                                    s == ki as int + 1, sz == (mi as int + 1) * s, mi >= 1, ki >= 1;
                            assert(mn * s + cc != mn * s + c);
                        }

                        assert forall |cc: int|
                            (c + 1) <= cc <= ki as int
                        implies
                            (#[trigger] prefix@[(max_num as int) * (stride as int) + cc]) == 0i64
                        by {
                            assert(0 <= mn * s + cc < sz as int) by(nonlinear_arith)
                                requires 1 <= mn <= mi as int, 0 <= cc <= ki as int,
                                    s == ki as int + 1, sz == (mi as int + 1) * s, mi >= 1, ki >= 1;
                            assert(mn * s + cc != mn * s + c);
                        }

                        assert forall |jj: int, cc: int|
                            1 <= jj < mn && 1 <= cc <= ki as int
                        implies
                            (#[trigger] dp@[jj * (stride as int) + cc])
                                == Self::dp_val_mod(l, jj, cc, mv) as i64
                        by {
                            assert(jj * s + cc < mn * s) by(nonlinear_arith)
                                requires jj < mn, cc < s, s == ki as int + 1;
                        }

                        assert forall |jj: int, cc: int|
                            1 <= jj < mn && 1 <= cc <= ki as int
                        implies
                            (#[trigger] prefix@[jj * (stride as int) + cc])
                                == Self::prefix_val_mod(l, jj, cc, mv) as i64
                        by {
                            assert(jj * s + cc < mn * s) by(nonlinear_arith)
                                requires jj < mn, cc < s, s == ki as int + 1;
                        }

                        assert forall |jj: int, cc: int|
                            (mn + 1) <= jj <= mi as int && 0 <= cc <= ki as int
                        implies
                            (#[trigger] dp@[jj * (stride as int) + cc]) == 0i64
                        by {
                            assert(0 <= jj * s + cc < sz as int) by(nonlinear_arith)
                                requires 1 <= jj <= mi as int, 0 <= cc <= ki as int,
                                    s == ki as int + 1, sz == (mi as int + 1) * s, mi >= 1, ki >= 1;
                            assert(cc < s);
                            assert(jj * s + cc >= (mn + 1) * s) by(nonlinear_arith)
                                requires jj >= mn + 1, s >= 1, cc >= 0;
                            assert((mn + 1) * s > mn * s + c) by(nonlinear_arith)
                                requires s > c, s >= 2;
                        }

                        assert forall |jj: int, cc: int|
                            (mn + 1) <= jj <= mi as int && 0 <= cc <= ki as int
                        implies
                            (#[trigger] prefix@[jj * (stride as int) + cc]) == 0i64
                        by {
                            assert(0 <= jj * s + cc < sz as int) by(nonlinear_arith)
                                requires 1 <= jj <= mi as int, 0 <= cc <= ki as int,
                                    s == ki as int + 1, sz == (mi as int + 1) * s, mi >= 1, ki >= 1;
                            assert(cc < s);
                            assert(jj * s + cc >= (mn + 1) * s) by(nonlinear_arith)
                                requires jj >= mn + 1, s >= 1, cc >= 0;
                            assert((mn + 1) * s > mn * s + c) by(nonlinear_arith)
                                requires s > c, s >= 2;
                        }

                        assert forall |cc: int| 0 <= cc <= ki as int
                        implies (#[trigger] dp@[cc]) == 0i64
                        by {
                            Self::row0_ne_set(cc, mn, s, c);
                        }
                        assert forall |cc: int| 0 <= cc <= ki as int
                        implies (#[trigger] prefix@[cc]) == 0i64
                        by {
                            Self::row0_ne_set(cc, mn, s, c);
                            assert(cc != mn * s + c);
                            assert((max_num * stride + cost) as int == mn * s + c);
                            assert(cc != (max_num * stride + cost) as int);
                            assert(snap_prefix_row0[cc] == 0i64);
                        }


                    }

                    cost = cost + 1;
                }
                max_num = max_num + 1;
            }
            prev_dp = dp;
            prev_prefix = prefix;
            len = len + 1;
        }

        proof {
            assert(mi * stride + ki < sz) by(nonlinear_arith)
                requires mi >= 1, ki >= 0, stride == ki + 1, sz == (mi + 1) * stride;
            if ki >= 1 && mi >= 1 {
                assert(prev_prefix@[(mi as int) * (stride as int) + (ki as int)]
                    == Self::prefix_val_mod(ni as int, mi as int, ki as int, modv as int) as i64);
                Self::dp_rec_mod_bounds(1, ni as int, mi as int, ki as int, modv as int);
            } else {
                if ki == 0 {
                    Self::prefix_val_zero_cost(ni as int, mi as int, modv as int);
                }
                Self::dp_rec_mod_bounds(1, ni as int, mi as int, ki as int, modv as int);
            }
        }

        prev_prefix[mi * stride + ki] as i32
    }
}

}
