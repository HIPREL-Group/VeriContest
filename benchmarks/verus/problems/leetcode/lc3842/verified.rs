use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bulb_on_prefix(bulbs: Seq<i32>, end: nat, bulb: int) -> bool
        recommends
            end <= bulbs.len(),
        decreases end,
    {
        if end == 0 {
            false
        } else if bulbs[end as int - 1] as int == bulb {
            !Self::bulb_on_prefix(bulbs, (end - 1) as nat, bulb)
        } else {
            Self::bulb_on_prefix(bulbs, (end - 1) as nat, bulb)
        }
    }

    proof fn lemma_bulb_on_prefix_step(bulbs: Seq<i32>, end: nat, bulb: int)
        requires
            end < bulbs.len(),
        ensures
            Self::bulb_on_prefix(bulbs, (end + 1) as nat, bulb) == if bulbs[end as int] as int == bulb {
                !Self::bulb_on_prefix(bulbs, end, bulb)
            } else {
                Self::bulb_on_prefix(bulbs, end, bulb)
            },
    {
    }

    pub fn toggle_light_bulbs(bulbs: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= bulbs.len() <= 100,
            forall|i: int| 0 <= i < bulbs.len() ==> 1 <= #[trigger] bulbs[i] <= 100,
        ensures
            forall|i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] as int && res[i] as int <= 100,
            forall|i: int, j: int| 0 <= i < j < res.len() ==> res[i] < res[j],
            forall|b: int| 1 <= b <= 100 ==> (
                (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == b)
                    <==> Self::bulb_on_prefix(bulbs@, bulbs.len() as nat, b)
            ),
    {
        let mut state: Vec<bool> = vec![false; 101];
        let mut i: usize = 0;
        while i < bulbs.len()
            invariant
                1 <= bulbs.len() <= 100,
                forall|j: int| 0 <= j < bulbs.len() ==> 1 <= #[trigger] bulbs[j] <= 100,
                state.len() == 101,
                0 <= i <= bulbs.len(),
                forall|b: int| 1 <= b <= 100 ==> state[b] == Self::bulb_on_prefix(bulbs@, i as nat, b),
            decreases bulbs.len() - i,
        {
            let b: usize = bulbs[i] as usize;
            let ghost old_state = state@;
            state.set(b, !state[b]);
            proof {
                assert(0 <= i as int);
                assert(i < bulbs.len());
                assert(1 <= bulbs[i as int] && bulbs[i as int] <= 100);
                assert(1 <= b && b <= 100);
                assert(b as int == bulbs[i as int] as int);
                assert forall|x: int| 1 <= x <= 100 implies state[x] == Self::bulb_on_prefix(bulbs@, (i + 1) as nat, x) by {
                    Self::lemma_bulb_on_prefix_step(bulbs@, i as nat, x);
                    if x == b as int {
                        assert(state[x] == !old_state[x]);
                        assert(old_state[x] == Self::bulb_on_prefix(bulbs@, i as nat, x));
                        assert(bulbs[i as int] as int == x);
                    } else {
                        assert(state[x] == old_state[x]);
                        assert(bulbs[i as int] as int != x);
                    }
                }
            }
            i = i + 1;
        }

        let mut res: Vec<i32> = Vec::new();
        let mut b: usize = 1;
        while b <= 100
            invariant
                1 <= b <= 101,
                state.len() == 101,
                forall|x: int| 1 <= x <= 100 ==> state[x] == Self::bulb_on_prefix(bulbs@, bulbs.len() as nat, x),
                forall|k: int| 0 <= k < res.len() ==> (1 <= #[trigger] res[k] as int) && ((res[k] as int) < (b as int)),
                forall|p: int, q: int| 0 <= p < q < res.len() ==> res[p] < res[q],
                forall|x: int| 1 <= x < (b as int) ==> (
                    state[x] <==> (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == x)
                ),
            decreases 101 - b,
        {
            let cur_b: usize = b;
            let ghost old_res = res@;
            proof {
                assert forall|x: int| 1 <= x < (cur_b as int) implies (
                    state[x] <==> (exists|k: int| 0 <= k < old_res.len() && #[trigger] old_res[k] as int == x)
                ) by {
                    assert(state[x] <==> (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == x));
                }
            }
            if state[cur_b] {
                res.push(cur_b as i32);
                proof {
                    assert(res@ == old_res.push(cur_b as i32));
                    assert forall|k: int| 0 <= k < old_res.len() implies (old_res[k] as int) < (cur_b as int) by {
                        assert(1 <= old_res[k] as int && (old_res[k] as int) < (cur_b as int));
                    }
                    assert forall|p: int, q: int| 0 <= p < q < res.len() implies res[p] < res[q] by {
                        if q < old_res.len() {
                            assert(res[p] == old_res[p]);
                            assert(res[q] == old_res[q]);
                        } else {
                            assert(q == old_res.len());
                            assert(res[q] as int == (cur_b as int));
                            assert(res[p] == old_res[p]);
                            assert((old_res[p] as int) < (cur_b as int));
                        }
                    }
                }
            }

            b = b + 1;
            proof {
                assert forall|k: int| 0 <= k < res.len() implies (1 <= #[trigger] res[k] as int) && ((res[k] as int) < (b as int)) by {
                    if state[cur_b as int] {
                        let old_len = res.len() - 1;
                        if k < old_len as int {
                            assert((res[k] as int) < (cur_b as int));
                        } else {
                            assert(k == old_len as int);
                            assert(res[k] as int == (cur_b as int));
                        }
                    } else {
                        assert((res[k] as int) < (cur_b as int));
                    }
                }

                assert forall|x: int| 1 <= x < (b as int) implies (
                    state[x] <==> (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == x)
                ) by {
                    if x < (cur_b as int) {
                        assert((exists|k: int| 0 <= k < res.len() && res[k] as int == x)
                            <==> (exists|k: int| 0 <= k < old_res.len() && old_res[k] as int == x)) by {
                            if state[cur_b as int] {
                                if exists|k: int| 0 <= k < res.len() && res[k] as int == x {
                                    let k = choose|k: int| 0 <= k < res.len() && res[k] as int == x;
                                    if k == old_res.len() {
                                        assert(res[k] as int == (cur_b as int));
                                        assert((cur_b as int) != x);
                                    }
                                }
                                if exists|k: int| 0 <= k < old_res.len() && old_res[k] as int == x {
                                    let k = choose|k: int| 0 <= k < old_res.len() && old_res[k] as int == x;
                                    assert(0 <= k < res.len());
                                    assert(res[k] as int == x);
                                }
                            } else {
                                assert(res@ == old_res);
                            }
                        }
                        assert(state[x] <==> (exists|k: int| 0 <= k < old_res.len() && old_res[k] as int == x));
                    } else {
                        assert(x == (cur_b as int));
                        if state[x] {
                            assert(exists|k: int| 0 <= k < res.len() && res[k] as int == x) by {
                                let k = res.len() - 1;
                                assert(0 <= k < res.len());
                                assert(res[k] as int == x);
                            }
                        } else {
                            assert(!(exists|k: int| 0 <= k < res.len() && res[k] as int == x)) by {
                                assert forall|k: int| 0 <= k < res.len() implies res[k] as int != x by {
                                    assert((res[k] as int) < (cur_b as int));
                                }
                            }
                        }
                    }
                }
            }
        }

        proof {
            assert(b == 101);
            assert forall|x: int| 1 <= x <= 100 implies (
                (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == x)
                    <==> Self::bulb_on_prefix(bulbs@, bulbs.len() as nat, x)
            ) by {
                assert(1 <= x && x < (b as int));
                assert(state[x] <==> (exists|k: int| 0 <= k < res.len() && res[k] as int == x));
                assert(state[x] == Self::bulb_on_prefix(bulbs@, bulbs.len() as nat, x));
            }
            assert forall|k: int| 0 <= k < res.len() implies 1 <= #[trigger] res[k] as int <= 100 by {
                assert(1 <= res[k] as int && (res[k] as int) < (b as int));
            }
        }

        res
    }
}

} 
