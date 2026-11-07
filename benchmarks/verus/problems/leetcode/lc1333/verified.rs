use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn passes_filter(
    restaurants: Seq<Vec<i32>>,
    i: int,
    vegan_friendly: i32,
    max_price: i32,
    max_distance: i32,
) -> bool {
    &&& (vegan_friendly == 0 || restaurants[i][2] == 1)
    &&& restaurants[i][3] <= max_price
    &&& restaurants[i][4] <= max_distance
}

pub open spec fn ranked_higher(
    restaurants: Seq<Vec<i32>>,
    a: int,
    b: int,
) -> bool {
    restaurants[a][1] > restaurants[b][1]
    || (restaurants[a][1] == restaurants[b][1] && restaurants[a][0] > restaurants[b][0])
}

pub open spec fn find_by_id(
    restaurants: Seq<Vec<i32>>,
    id: i32,
    n: int,
) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else if restaurants[n - 1][0] == id {
        n - 1
    } else {
        find_by_id(restaurants, id, n - 1)
    }
}

proof fn lemma_find_by_id_correct(
    restaurants: Seq<Vec<i32>>,
    id: i32,
    n: int,
)
    requires
        0 < n <= restaurants.len(),
        exists |i: int| 0 <= i < n && restaurants[i][0] == id,
    ensures
        0 <= find_by_id(restaurants, id, n) < n,
        restaurants[find_by_id(restaurants, id, n)][0] == id,
    decreases n,
{
    if restaurants[n - 1][0] == id {
    } else {
        lemma_find_by_id_correct(restaurants, id, n - 1);
    }
}

proof fn lemma_find_by_id_unique(
    restaurants: Seq<Vec<i32>>,
    id: i32,
    n: int,
    target: int,
)
    requires
        0 <= target < n <= restaurants.len(),
        restaurants[target][0] == id,
        forall |i: int, j: int|
            0 <= i < j < n ==> restaurants[i][0] != restaurants[j][0],
    ensures
        find_by_id(restaurants, id, n) == target,
    decreases n,
{
    if n <= 0 {
    } else if restaurants[n - 1][0] == id {
        if target != n - 1 {
            if target < n - 1 {
                assert(restaurants[target][0] != restaurants[n - 1][0]);
            }
        }
    } else {
        lemma_find_by_id_unique(restaurants, id, n - 1, target);
    }
}

pub open spec fn is_reorder_of(r: Seq<int>, p: Seq<usize>, s: Seq<usize>) -> bool {
    &&& r.len() == s.len()
    &&& p.len() == s.len()
    &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
    &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
    &&& forall |i: int| 0 <= i < p.len() ==> p[i] == s[#[trigger] r[i]]
}

impl Solution {
    pub fn filter_restaurants(
        restaurants: Vec<Vec<i32>>,
        vegan_friendly: i32,
        max_price: i32,
        max_distance: i32,
    ) -> (result: Vec<i32>)
        requires
            1 <= restaurants.len() <= 10000,
            forall |i: int| #![trigger restaurants[i]]
                0 <= i < restaurants.len() ==> {
                    &&& restaurants[i].len() == 5
                    &&& 1 <= restaurants[i][0] <= 100000
                    &&& 1 <= restaurants[i][1] <= 100000
                    &&& (restaurants[i][2] == 0 || restaurants[i][2] == 1)
                    &&& 1 <= restaurants[i][3] <= 100000
                    &&& 1 <= restaurants[i][4] <= 100000
                },
            vegan_friendly == 0 || vegan_friendly == 1,
            1 <= max_price <= 100000,
            1 <= max_distance <= 100000,
            forall |i: int, j: int|
                0 <= i < j < restaurants.len()
                ==> restaurants[i][0] != restaurants[j][0],
        ensures
            forall |j: int| 0 <= j < result.len() ==>
                0 <= find_by_id(restaurants@, #[trigger] result[j], restaurants@.len() as int)
                    < restaurants@.len(),
            forall |j: int| 0 <= j < result.len() ==>
                passes_filter(
                    restaurants@,
                    find_by_id(restaurants@, #[trigger] result[j], restaurants@.len() as int),
                    vegan_friendly,
                    max_price,
                    max_distance,
                ),
            forall |i: int| #![trigger restaurants[i]]
                0 <= i < restaurants.len()
                && passes_filter(restaurants@, i, vegan_friendly, max_price, max_distance)
                ==> exists |j: int|
                    0 <= j < result.len() && result[j] == restaurants[i][0],
            forall |j: int, k: int|
                0 <= j < k < result.len() ==> result[j] != result[k],
            forall |j: int, k: int|
                0 <= j < k < result.len() ==>
                ranked_higher(
                    restaurants@,
                    find_by_id(restaurants@, result[j], restaurants@.len() as int),
                    find_by_id(restaurants@, result[k], restaurants@.len() as int),
                ),
    {
        let n = restaurants.len();
        let ghost rs = restaurants@;

        
        let mut indices: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == restaurants.len(),
                rs == restaurants@,
                0 <= i <= n,
                forall |ii: int| #![trigger restaurants[ii]] 0 <= ii < n as int ==> {
                    &&& restaurants[ii].len() == 5
                    &&& 1 <= restaurants[ii][0] <= 100000
                    &&& 1 <= restaurants[ii][1] <= 100000
                    &&& (restaurants[ii][2] == 0 || restaurants[ii][2] == 1)
                    &&& 1 <= restaurants[ii][3] <= 100000
                    &&& 1 <= restaurants[ii][4] <= 100000
                },
                forall |ii: int, jj: int| 0 <= ii < jj < n as int ==> restaurants[ii][0] != restaurants[jj][0],
                forall |p: int| 0 <= p < indices.len() ==>
                    0 <= #[trigger] indices[p] < n,
                forall |p: int| 0 <= p < indices.len() ==>
                    passes_filter(rs, #[trigger] indices[p] as int, vegan_friendly, max_price, max_distance),
                forall |p: int| 0 <= p < indices.len() ==>
                    (#[trigger] indices[p] as int) < i as int,
                forall |p: int, q: int| 0 <= p < q < indices.len() ==>
                    indices[p] != indices[q],
                forall |t: int| 0 <= t < i as int
                    && passes_filter(rs, t, vegan_friendly, max_price, max_distance)
                    ==> exists |p: int| 0 <= p < indices.len()
                        && #[trigger] indices[p] == t as usize,
            decreases n - i,
        {
            let ghost old_indices_len = indices@.len();
            let ghost old_indices_snap = indices@;
            if (vegan_friendly == 0 || restaurants[i][2] == 1)
                && restaurants[i][3] <= max_price
                && restaurants[i][4] <= max_distance
            {
                proof {
                    assert(passes_filter(rs, i as int, vegan_friendly, max_price, max_distance));
                    assert forall |p: int| 0 <= p < indices@.len() implies
                        indices[p] != i by {
                        assert((indices[p] as int) < i as int);
                    }
                }
                indices.push(i);
                proof {
                    assert(indices@[old_indices_len as int] == i as usize);
                    assert forall |t: int| 0 <= t < i as int + 1
                        && passes_filter(rs, t, vegan_friendly, max_price, max_distance)
                        implies exists |p: int| 0 <= p < indices@.len()
                            && #[trigger] indices@[p] == t as usize by {
                        if t == i as int {
                            assert(indices@[old_indices_len as int] == t as usize);
                        } else {
                            let p0 = choose |pp: int| 0 <= pp < old_indices_len as int
                                && old_indices_snap[pp] == t as usize;
                            assert(indices@[p0] == old_indices_snap[p0]);
                            assert(indices@[p0] == t as usize);
                        }
                    }
                }
            } else {
                proof {
                    assert(!passes_filter(rs, i as int, vegan_friendly, max_price, max_distance));
                }
            }
            i += 1;
        }

        let m = indices.len();
        let ghost pre_sort = indices@;
        proof {
            let r_id = Seq::new(pre_sort.len(), |i: int| i);
            assert forall |i: int| 0 <= i < pre_sort.len() implies
                pre_sort[i] == pre_sort[#[trigger] r_id[i]] by {}
            assert(is_reorder_of(r_id, pre_sort, pre_sort));
        }

        
        let mut j: usize = 0;
        while j < m
            invariant
                n == restaurants.len(),
                rs == restaurants@,
                m == indices.len(),
                0 <= j <= m,
                forall |ii: int| #![trigger restaurants[ii]] 0 <= ii < n as int ==> {
                    &&& restaurants[ii].len() == 5
                    &&& 1 <= restaurants[ii][0] <= 100000
                    &&& 1 <= restaurants[ii][1] <= 100000
                    &&& (restaurants[ii][2] == 0 || restaurants[ii][2] == 1)
                    &&& 1 <= restaurants[ii][3] <= 100000
                    &&& 1 <= restaurants[ii][4] <= 100000
                },
                forall |ii: int, jj: int| 0 <= ii < jj < n as int ==> restaurants[ii][0] != restaurants[jj][0],
                exists |r: Seq<int>| is_reorder_of(r, indices@, pre_sort),
                forall |p: int| 0 <= p < m ==>
                    0 <= #[trigger] indices[p] < n,
                forall |p: int| 0 <= p < m ==>
                    passes_filter(rs, #[trigger] indices[p] as int, vegan_friendly, max_price, max_distance),
                forall |p: int, q: int| 0 <= p < q < m ==>
                    indices[p] != indices[q],
                forall |t: int| 0 <= t < n as int
                    && passes_filter(rs, t, vegan_friendly, max_price, max_distance)
                    ==> exists |p: int| 0 <= p < m
                        && #[trigger] indices[p] == t as usize,
                forall |p: int, q: int| 0 <= p < q < j as int ==>
                    ranked_higher(rs, indices[p] as int, indices[q] as int),
                forall |p: int, q: int| 0 <= p < j as int && j as int <= q < m ==>
                    ranked_higher(rs, indices[p] as int, indices[q] as int),
            decreases m - j,
        {
            let mut best: usize = j;
            let mut k: usize = j + 1;
            while k < m
                invariant
                    n == restaurants.len(),
                    rs == restaurants@,
                    m == indices.len(),
                    0 <= j < m,
                    j <= best < k <= m,
                    forall |ii: int| #![trigger restaurants[ii]] 0 <= ii < n as int ==> {
                        &&& restaurants[ii].len() == 5
                        &&& 1 <= restaurants[ii][0] <= 100000
                        &&& 1 <= restaurants[ii][1] <= 100000
                        &&& (restaurants[ii][2] == 0 || restaurants[ii][2] == 1)
                        &&& 1 <= restaurants[ii][3] <= 100000
                        &&& 1 <= restaurants[ii][4] <= 100000
                    },
                    forall |ii: int, jj: int| 0 <= ii < jj < n as int ==> restaurants[ii][0] != restaurants[jj][0],
                    forall |p: int| 0 <= p < m ==>
                        0 <= #[trigger] indices[p] < n,
                    forall |p: int, q: int| 0 <= p < q < m ==>
                        indices[p] != indices[q],
                    forall |q: int| j as int <= q < k as int ==>
                        ranked_higher(rs, indices[best as int] as int, indices[q] as int)
                        || indices[best as int] == indices[q],
                decreases m - k,
            {
                let ik = indices[k];
                let ib = indices[best];
                if restaurants[ik][1] > restaurants[ib][1]
                    || (restaurants[ik][1] == restaurants[ib][1]
                        && restaurants[ik][0] > restaurants[ib][0])
                {
                    best = k;
                    proof {
                        assert forall |q: int| j as int <= q < k as int + 1 implies
                            ranked_higher(rs, indices[best as int] as int, indices[q] as int)
                            || indices[best as int] == indices[q] by {
                            if q < k as int {
                                let iq_idx = indices[q] as int;
                                let ib_idx = ib as int;
                                let ik_idx = ik as int;
                                if indices[best as int] != indices[q] {
                                    if ib == indices[q] as usize {
                                        assert(ranked_higher(rs, ik_idx, iq_idx));
                                    } else {
                                        if rs[ib_idx][1] > rs[iq_idx][1] {
                                            assert(rs[ik_idx][1] >= rs[ib_idx][1]);
                                            assert(ranked_higher(rs, ik_idx, iq_idx));
                                        } else if rs[ib_idx][1] == rs[iq_idx][1] && rs[ib_idx][0] > rs[iq_idx][0] {
                                            if rs[ik_idx][1] > rs[ib_idx][1] {
                                                assert(ranked_higher(rs, ik_idx, iq_idx));
                                            } else {
                                                assert(rs[ik_idx][0] > rs[ib_idx][0]);
                                                assert(ranked_higher(rs, ik_idx, iq_idx));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                k += 1;
            }

            
            let val_j = indices[j];
            let val_best = indices[best];
            let ghost old_indices = indices@;

            proof {
                
                assert forall |p: int, q: int| 0 <= p < q < j as int implies
                    ranked_higher(rs, old_indices[p] as int, old_indices[q] as int) by {}
                assert forall |p: int, q: int| 0 <= p < j as int && j as int <= q < m implies
                    ranked_higher(rs, old_indices[p] as int, old_indices[q] as int) by {}
                assert forall |q: int| j as int <= q < m implies
                    ranked_higher(rs, old_indices[best as int] as int, old_indices[q] as int)
                    || old_indices[best as int] == old_indices[q] by {}
                assert forall |p: int, q: int| 0 <= p < q < m implies
                    old_indices[p] != old_indices[q] by {}

                
                let r1 = choose |r: Seq<int>| is_reorder_of(r, indices@, pre_sort);
                let r2 = r1.update(j as int, r1[best as int]).update(best as int, r1[j as int]);
                let new_ind = indices@.update(j as int, val_best).update(best as int, val_j);
                assert forall |p: int| 0 <= p < m implies
                    new_ind[p] == pre_sort[#[trigger] r2[p]] by {
                    if p == j as int {
                        assert(r2[p] == r1[best as int]);
                        assert(new_ind[p] == val_best);
                        assert(val_best == indices@[best as int]);
                        assert(indices@[best as int] == pre_sort[r1[best as int]]);
                    } else if p == best as int {
                        assert(r2[p] == r1[j as int]);
                        assert(new_ind[p] == val_j);
                        assert(val_j == indices@[j as int]);
                        assert(indices@[j as int] == pre_sort[r1[j as int]]);
                    } else {
                        assert(r2[p] == r1[p]);
                        assert(new_ind[p] == indices@[p]);
                        assert(indices@[p] == pre_sort[r1[p]]);
                    }
                }
                assert forall |p: int, q: int| 0 <= p < q < m as int implies
                    r2[p] != r2[q] by {
                    if p == j as int && q == best as int {
                        assert(r2[p] == r1[best as int]);
                        assert(r2[q] == r1[j as int]);
                    } else if p == j as int {
                        assert(r2[p] == r1[best as int]);
                        assert(r2[q] == r1[q]);
                    } else if p == best as int {
                        assert(r2[p] == r1[j as int]);
                        assert(r2[q] == r1[q]);
                    } else if q == j as int {
                        assert(r2[p] == r1[p]);
                        assert(r2[q] == r1[best as int]);
                    } else if q == best as int {
                        assert(r2[p] == r1[p]);
                        assert(r2[q] == r1[j as int]);
                    } else {
                        assert(r2[p] == r1[p]);
                        assert(r2[q] == r1[q]);
                    }
                }
                assert forall |p: int| 0 <= p < r2.len() implies
                    0 <= #[trigger] r2[p] < r2.len() by {
                    if p == j as int {
                        assert(r2[p] == r1[best as int]);
                    } else if p == best as int {
                        assert(r2[p] == r1[j as int]);
                    } else {
                        assert(r2[p] == r1[p]);
                    }
                }
                assert(is_reorder_of(r2, new_ind, pre_sort));
                assert forall |p: int, q: int| 0 <= p < q < m implies
                    new_ind[p] != new_ind[q] by {
                    if p == j as int && q == best as int {
                    } else if p == j as int {
                        assert(new_ind[p] == indices@[best as int]);
                        assert(new_ind[q] == indices@[q]);
                    } else if p == best as int {
                        assert(new_ind[p] == indices@[j as int]);
                        assert(new_ind[q] == indices@[q]);
                    } else if q == j as int {
                        assert(new_ind[p] == indices@[p]);
                        assert(new_ind[q] == indices@[best as int]);
                    } else if q == best as int {
                        assert(new_ind[p] == indices@[p]);
                        assert(new_ind[q] == indices@[j as int]);
                    } else {
                        assert(new_ind[p] == indices@[p]);
                        assert(new_ind[q] == indices@[q]);
                    }
                }
                assert forall |t: int| 0 <= t < n as int
                    && passes_filter(rs, t, vegan_friendly, max_price, max_distance)
                    implies exists |p: int| 0 <= p < m
                        && #[trigger] new_ind[p] == t as usize by {
                    let p0 = choose |p: int| 0 <= p < m && indices[p] == t as usize;
                    if p0 == j as int {
                        assert(new_ind[best as int] == t as usize);
                    } else if p0 == best as int {
                        assert(new_ind[j as int] == t as usize);
                    } else {
                        assert(new_ind[p0] == t as usize);
                    }
                }
            }
            indices.set(j, val_best);
            indices.set(best, val_j);

            proof {
                
                
                

                
                assert forall |p: int, q: int| 0 <= p < q < j as int + 1 implies
                    ranked_higher(rs, indices[p] as int, indices[q] as int) by {
                    if q < j as int {
                        
                        assert(indices@[p] == old_indices[p]);
                        assert(indices@[q] == old_indices[q]);
                    } else {
                        
                        assert(indices@[p] == old_indices[p]);
                        assert(indices@[j as int] == val_best);
                        assert(val_best == old_indices[best as int]);
                        
                        assert(ranked_higher(rs, old_indices[p] as int, old_indices[best as int] as int));
                    }
                }

                
                assert forall |p: int, q: int| 0 <= p < j as int + 1 && j as int + 1 <= q < m implies
                    ranked_higher(rs, indices[p] as int, indices[q] as int) by {
                    if p < j as int {
                        
                        assert(indices@[p] == old_indices[p]);
                        if q == best as int {
                            
                            assert(indices@[best as int] == val_j);
                            assert(val_j == old_indices[j as int]);
                            
                            assert(ranked_higher(rs, old_indices[p] as int, old_indices[j as int] as int));
                        } else {
                            
                            assert(indices@[q] == old_indices[q]);
                            
                            assert(ranked_higher(rs, old_indices[p] as int, old_indices[q] as int));
                        }
                    } else {
                        
                        assert(indices@[j as int] == val_best);
                        assert(val_best == old_indices[best as int]);
                        if q == best as int {
                            
                            assert(indices@[best as int] == val_j);
                            assert(val_j == old_indices[j as int]);
                            
                            assert(old_indices[best as int] != old_indices[j as int]);
                            
                            assert(ranked_higher(rs, old_indices[best as int] as int, old_indices[j as int] as int));
                        } else {
                            
                            assert(indices@[q] == old_indices[q]);
                            
                            assert(old_indices[best as int] != old_indices[q]);
                            
                            assert(ranked_higher(rs, old_indices[best as int] as int, old_indices[q] as int));
                        }
                    }
                }
            }
            j += 1;
        }

        
        let mut result: Vec<i32> = Vec::new();
        let mut l: usize = 0;
        while l < m
            invariant
                n == restaurants.len(),
                rs == restaurants@,
                m == indices.len(),
                0 <= l <= m,
                result.len() == l as int,
                forall |ii: int| #![trigger restaurants[ii]] 0 <= ii < n as int ==> {
                    &&& restaurants[ii].len() == 5
                    &&& 1 <= restaurants[ii][0] <= 100000
                    &&& 1 <= restaurants[ii][1] <= 100000
                    &&& (restaurants[ii][2] == 0 || restaurants[ii][2] == 1)
                    &&& 1 <= restaurants[ii][3] <= 100000
                    &&& 1 <= restaurants[ii][4] <= 100000
                },
                forall |ii: int, jj: int| 0 <= ii < jj < n as int ==> restaurants[ii][0] != restaurants[jj][0],
                forall |p: int| 0 <= p < m ==>
                    0 <= #[trigger] indices[p] < n,
                forall |p: int| 0 <= p < m ==>
                    passes_filter(rs, #[trigger] indices[p] as int, vegan_friendly, max_price, max_distance),
                forall |p: int, q: int| 0 <= p < q < m ==>
                    indices[p] != indices[q],
                forall |t: int| 0 <= t < n as int
                    && passes_filter(rs, t, vegan_friendly, max_price, max_distance)
                    ==> exists |p: int| 0 <= p < m
                        && #[trigger] indices[p] == t as usize,
                forall |p: int, q: int| 0 <= p < q < m ==>
                    ranked_higher(rs, indices[p] as int, indices[q] as int),
                forall |p: int| 0 <= p < l as int ==>
                    #[trigger] result[p] == rs[indices[p] as int][0],
            decreases m - l,
        {
            result.push(restaurants[indices[l]][0]);
            l += 1;
        }

        proof {
            let nn = rs.len() as int;
            assert forall |jj: int| 0 <= jj < result.len() implies
                0 <= find_by_id(rs, #[trigger] result[jj], nn) < nn by {
                let idx = indices[jj] as int;
                assert(result[jj] == rs[idx][0]);
                lemma_find_by_id_correct(rs, result[jj], nn);
            }
            assert forall |jj: int| 0 <= jj < result.len() implies
                passes_filter(
                    rs,
                    find_by_id(rs, #[trigger] result[jj], nn),
                    vegan_friendly,
                    max_price,
                    max_distance,
                ) by {
                let idx = indices[jj] as int;
                assert(result[jj] == rs[idx][0]);
                lemma_find_by_id_unique(rs, result[jj], nn, idx);
            }
            assert forall |ii: int| #![trigger restaurants[ii]]
                0 <= ii < restaurants.len()
                && passes_filter(rs, ii, vegan_friendly, max_price, max_distance)
                implies exists |jj: int|
                    0 <= jj < result.len() && result[jj] == restaurants[ii][0] by {
                let p = choose |p: int| 0 <= p < m && indices[p] == ii as usize;
                assert(result[p] == rs[indices[p] as int][0]);
            }
            assert forall |jj: int, kk: int|
                0 <= jj < kk < result.len() implies result[jj] != result[kk] by {
                let ij = indices[jj] as int;
                let ik = indices[kk] as int;
                assert(result[jj] == rs[ij][0]);
                assert(result[kk] == rs[ik][0]);
                assert(indices[jj] != indices[kk]);
                if ij < ik {
                    assert(rs[ij][0] != rs[ik][0]);
                } else {
                    assert(rs[ik][0] != rs[ij][0]);
                }
            }
            assert forall |jj: int, kk: int|
                0 <= jj < kk < result.len() implies
                ranked_higher(
                    rs,
                    find_by_id(rs, result[jj], nn),
                    find_by_id(rs, result[kk], nn),
                ) by {
                let ij = indices[jj] as int;
                let ik = indices[kk] as int;
                assert(result[jj] == rs[ij][0]);
                assert(result[kk] == rs[ik][0]);
                lemma_find_by_id_unique(rs, result[jj], nn, ij);
                lemma_find_by_id_unique(rs, result[kk], nn, ik);
            }
        }
        result
    }
}

}
