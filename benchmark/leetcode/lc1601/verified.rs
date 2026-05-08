use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 }
    else { 2 * pow2(n - 1) }
}

pub open spec fn bit_set(mask: int, j: int) -> bool {
    (mask / pow2(j)) % 2 == 1
}

pub open spec fn count_ones(mask: int, len: int) -> int
    decreases len,
{
    if len <= 0 { 0 }
    else {
        count_ones(mask, len - 1) + if bit_set(mask, len - 1) { 1int } else { 0int }
    }
}

pub open spec fn net_change_for(requests: Seq<Vec<i32>>, mask: int, building: int, len: int) -> int
    decreases len,
{
    if len <= 0 { 0 }
    else {
        let prev = net_change_for(requests, mask, building, len - 1);
        if bit_set(mask, len - 1) {
            prev
            - (if requests[len - 1][0] as int == building { 1int } else { 0int })
            + (if requests[len - 1][1] as int == building { 1int } else { 0int })
        } else {
            prev
        }
    }
}

pub open spec fn is_balanced(requests: Seq<Vec<i32>>, mask: int, n: int, m: int) -> bool {
    forall|b: int| 0 <= b < n ==> net_change_for(requests, mask, b, m) == 0
}

proof fn pow2_positive(n: int)
    requires n >= 0,
    ensures pow2(n) >= 1,
    decreases n,
{
    if n > 0 {
        pow2_positive(n - 1);
    }
}

proof fn pow2_mono(a: int, b: int)
    requires 0 <= a <= b,
    ensures pow2(a) <= pow2(b),
    decreases b - a,
{
    if a < b {
        pow2_mono(a, b - 1);
        pow2_positive(b - 1);
    }
}

proof fn pow2_bound(n: int)
    requires 0 <= n <= 16,
    ensures pow2(n) <= 65536,
{
    pow2_mono(n, 16);
    reveal_with_fuel(pow2, 17);
    assert(pow2(16) <= 65536);
}

proof fn count_ones_bound(mask: int, len: int)
    requires len >= 0,
    ensures 0 <= count_ones(mask, len) <= len,
    decreases len,
{
    if len > 0 {
        count_ones_bound(mask, len - 1);
    }
}

proof fn count_ones_zero_mask(len: int)
    requires len >= 0,
    ensures count_ones(0, len) == 0,
    decreases len,
{
    if len > 0 {
        count_ones_zero_mask(len - 1);
        pow2_positive(len - 1);
    }
}

proof fn net_change_zero_mask(requests: Seq<Vec<i32>>, building: int, len: int)
    requires len >= 0,
    ensures net_change_for(requests, 0, building, len) == 0,
    decreases len,
{
    if len > 0 {
        net_change_zero_mask(requests, building, len - 1);
        pow2_positive(len - 1);
    }
}

proof fn net_change_bound(requests: Seq<Vec<i32>>, mask: int, building: int, len: int)
    requires
        len >= 0,
        len <= requests.len(),
        forall|i: int| 0 <= i < requests.len() ==>
            #[trigger] requests[i].len() == 2,
    ensures
        -len <= net_change_for(requests, mask, building, len) <= len,
    decreases len,
{
    if len > 0 {
        net_change_bound(requests, mask, building, len - 1);
    }
}

impl Solution {
    pub fn maximum_requests(n: i32, requests: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= n <= 20,
            1 <= requests.len() <= 16,
            forall|i: int| 0 <= i < requests.len() ==>
                #[trigger] requests[i].len() == 2
                && 0 <= requests[i][0] < n
                && 0 <= requests[i][1] < n,
        ensures
            0 <= result as int <= requests.len(),
            exists|mask: int| 0 <= mask < pow2(requests.len() as int)
                && is_balanced(requests@, mask, n as int, requests.len() as int)
                && result as int == count_ones(mask, requests.len() as int),
            forall|mask: int| (0 <= mask < pow2(requests.len() as int)
                && is_balanced(requests@, mask, n as int, requests.len() as int))
                ==> count_ones(mask, requests.len() as int) <= result as int,
    {
        let m = requests.len();

        let mut total: u32 = 1;
        let mut p: usize = 0;
        while p < m
            invariant
                0 <= p <= m,
                total as int == pow2(p as int),
                m == requests.len(),
                m <= 16,
            decreases m - p,
        {
            proof { pow2_bound((p + 1) as int); }
            total = total * 2;
            p += 1;
        }

        let mut net: Vec<i32> = Vec::new();
        let mut init_k: usize = 0;
        while init_k < n as usize
            invariant
                0 <= init_k <= n as usize,
                net.len() == init_k,
                forall|k: int| 0 <= k < init_k as int ==> net[k] == 0i32,
            decreases n as usize - init_k,
        {
            net.push(0i32);
            init_k += 1;
        }

        let mut best: i32 = 0;
        let ghost mut best_mask: int = 0;

        proof {
            assert forall|b: int| 0 <= b < n as int
                implies net_change_for(requests@, 0, b, m as int) == 0
            by {
                net_change_zero_mask(requests@, b, m as int);
            };
            count_ones_zero_mask(m as int);
            pow2_positive(m as int);
        }

        let mut mask: u32 = 0;
        while mask < total
            invariant
                0 <= mask as int <= pow2(m as int),
                total as int == pow2(m as int),
                m == requests.len(),
                m <= 16,
                1 <= n <= 20,
                net.len() == n as usize,
                forall|i: int| 0 <= i < m as int ==>
                    #[trigger] requests[i].len() == 2
                    && 0 <= requests[i][0] < n
                    && 0 <= requests[i][1] < n,
                0 <= best_mask < pow2(m as int),
                is_balanced(requests@, best_mask, n as int, m as int),
                best as int == count_ones(best_mask, m as int),
                0 <= best as int <= m as int,
                forall|mk: int| (0 <= mk < mask as int
                    && is_balanced(requests@, mk, n as int, m as int))
                    ==> count_ones(mk, m as int) <= best as int,
            decreases pow2(m as int) - mask as int,
        {
            let mut r: usize = 0;
            while r < n as usize
                invariant
                    0 <= r <= n as usize,
                    net.len() == n as usize,
                    forall|k: int| 0 <= k < r as int ==> net[k] == 0i32,
                decreases n as usize - r,
            {
                net.set(r, 0i32);
                r += 1;
            }

            let mut count: i32 = 0;
            let mut j: usize = 0;
            let mut pow_j: u32 = 1;
            while j < m
                invariant
                    0 <= j <= m,
                    m == requests.len(),
                    m <= 16,
                    pow_j as int == pow2(j as int),
                    net.len() == n as usize,
                    1 <= n <= 20,
                    mask < total,
                    total as int == pow2(m as int),
                    count as int == count_ones(mask as int, j as int),
                    0 <= count as int <= j as int,
                    forall|b: int| 0 <= b < n as int ==>
                        #[trigger] net[b] as int == net_change_for(requests@, mask as int, b, j as int),
                    forall|b: int| 0 <= b < n as int ==> -(j as int) <= #[trigger] net[b] <= j as int,
                    forall|i: int| 0 <= i < m as int ==>
                        #[trigger] requests[i].len() == 2
                        && 0 <= requests[i][0] < n
                        && 0 <= requests[i][1] < n,
                decreases m - j,
            {
                proof {
                    pow2_positive(j as int);
                }

                if (mask / pow_j) % 2 == 1 {
                    proof {
                        assert(bit_set(mask as int, j as int));
                        assert(requests[j as int].len() == 2);
                    }

                    let from_b = requests[j][0] as usize;
                    let to_b = requests[j][1] as usize;

                    let ghost pre_net = net@;

                    let old_from = net[from_b];
                    net.set(from_b, old_from - 1);

                    let cur_to = net[to_b];
                    net.set(to_b, cur_to + 1);

                    count += 1;

                    proof {
                        assert forall|b: int| 0 <= b < n as int implies
                            #[trigger] net@[b] as int == net_change_for(requests@, mask as int, b, (j + 1) as int)
                        by {
                            assert(pre_net[b] as int == net_change_for(requests@, mask as int, b, j as int));
                            if b == from_b as int && b == to_b as int {
                                assert(net@[b] == pre_net[b]);
                            } else if b == from_b as int {
                                assert(net@[b] as int == pre_net[b] as int - 1);
                            } else if b == to_b as int {
                                assert(net@[b] as int == pre_net[b] as int + 1);
                            } else {
                                assert(net@[b] == pre_net[b]);
                            }
                        };
                        count_ones_bound(mask as int, (j + 1) as int);
                    }
                } else {
                    proof {
                        assert(!bit_set(mask as int, j as int));
                        assert forall|b: int| 0 <= b < n as int implies
                            #[trigger] net@[b] as int == net_change_for(requests@, mask as int, b, (j + 1) as int)
                        by {};
                    }
                }

                proof {
                    pow2_bound((j + 1) as int);
                    assert forall|b: int| 0 <= b < n as int implies
                        -((j + 1) as int) <= #[trigger] net@[b] <= (j + 1) as int
                    by {
                        net_change_bound(requests@, mask as int, b, (j + 1) as int);
                        assert(net@[b] as int == net_change_for(requests@, mask as int, b, (j + 1) as int));
                    };
                }

                pow_j = pow_j * 2;
                j += 1;
            }

            let mut balanced: bool = true;
            let mut k: usize = 0;
            while k < n as usize
                invariant
                    0 <= k <= n as usize,
                    net.len() == n as usize,
                    1 <= n <= 20,
                    forall|b: int| 0 <= b < n as int ==>
                        #[trigger] net@[b] as int == net_change_for(requests@, mask as int, b, m as int),
                    balanced == (forall|b: int| 0 <= b < k as int ==> net[b] == 0i32),
                    m == requests.len(),
                decreases n as usize - k,
            {
                if net[k] != 0 {
                    balanced = false;
                }
                k += 1;
            }

            proof {
                if balanced {
                    assert forall|b: int| 0 <= b < n as int implies
                        net_change_for(requests@, mask as int, b, m as int) == 0
                    by {
                        assert(net@[b] == 0i32);
                    };
                    assert(is_balanced(requests@, mask as int, n as int, m as int));
                }
            }

            if balanced && count > best {
                best = count;
                proof {
                    best_mask = mask as int;
                }
            }

            proof {
                pow2_bound(m as int);
                assert forall|mk: int| (0 <= mk < mask as int + 1
                    && is_balanced(requests@, mk, n as int, m as int))
                    implies count_ones(mk, m as int) <= best as int
                by {
                    if mk < mask as int {
                    } else {
                        assert(mk == mask as int);
                        if balanced {
                        } else {
                            let witness_b = choose|b: int| 0 <= b < n as int && net@[b] != 0i32;
                            assert(0 <= witness_b < n as int && net@[witness_b] != 0i32);
                            assert(net_change_for(requests@, mask as int, witness_b, m as int) != 0);
                            assert(!is_balanced(requests@, mk, n as int, m as int));
                        }
                    }
                };
            }

            mask += 1;
        }

        best
    }
}

}
