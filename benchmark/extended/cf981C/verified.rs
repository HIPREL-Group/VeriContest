use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_occ(u_edges: Seq<usize>, v_edges: Seq<usize>, v: usize, end: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        let u_val = u_edges[end - 1];
        let v_val = v_edges[end - 1];
        let add: int = if u_val == v && v_val == v { 2 } else if u_val == v || v_val == v { 1 } else { 0 };
        count_occ(u_edges, v_edges, v, end - 1) + add
    }
}

pub open spec fn spec_count_high_deg(u_edges: Seq<usize>, v_edges: Seq<usize>, v_start: int, v_end: int) -> int
    decreases v_end - v_start
{
    if v_end <= v_start {
        0
    } else {
        let add: int = if count_occ(u_edges, v_edges, (v_end - 1) as usize, u_edges.len() as int) >= 3 { 1 } else { 0 };
        spec_count_high_deg(u_edges, v_edges, v_start, v_end - 1) + add
    }
}

pub open spec fn is_valid_result(n: usize, u_edges: Seq<usize>, v_edges: Seq<usize>, has_solution: bool, center: usize) -> bool {
    let high = spec_count_high_deg(u_edges, v_edges, 1, n as int + 1);
    if high > 1 {
        !has_solution
    } else {
        has_solution &&
        1 <= center && center <= n &&
        (high == 1 ==> count_occ(u_edges, v_edges, center, u_edges.len() as int) >= 3)
    }
}

pub open spec fn is_valid_leaves(n: usize, u_edges: Seq<usize>, v_edges: Seq<usize>, center: usize, leaves: Seq<usize>) -> bool {
    (forall|k: int| 0 <= k && k < leaves.len() ==>
        1 <= leaves[k] && leaves[k] <= n &&
        leaves[k] != center &&
        count_occ(u_edges, v_edges, leaves[k] as usize, u_edges.len() as int) == 1)
    &&
    (forall|v: int| 1 <= v && v <= n ==> {
        let occ = #[trigger] count_occ(u_edges, v_edges, v as usize, u_edges.len() as int);
        (occ == 1 && v != center as int) ==>
            (exists|k: int| 0 <= k && k < leaves.len() && #[trigger] leaves[k] == v as usize)
    })
}

pub struct Solution;

impl Solution {
    pub fn useful_decomposition(n: usize, u_edges: Vec<usize>, v_edges: Vec<usize>) -> (res: (bool, usize, Vec<usize>))
        requires
            1 <= n && n <= 100000,
            u_edges.len() == n - 1,
            v_edges.len() == n - 1,
            forall|j: int| 0 <= j && j < n - 1 ==> 1 <= u_edges@[j] && u_edges@[j] <= n,
            forall|j: int| 0 <= j && j < n - 1 ==> 1 <= v_edges@[j] && v_edges@[j] <= n,
        ensures
            is_valid_result(n, u_edges@, v_edges@, res.0, res.1),
            res.0 ==> is_valid_leaves(n, u_edges@, v_edges@, res.1, res.2@)
    {
        let mut degrees: Vec<i32> = Vec::new();
        let mut i = 0;
        while i <= n
            invariant
                0 <= i && i <= n + 1,
                n <= 100000,
                degrees.len() == i,
                forall|k: int| 0 <= k && k < i ==> degrees@[k] == 0,
            decreases n + 1 - i
        {
            degrees.push(0);
            i += 1;
        }

        i = 0;
        while i < n - 1
            invariant
                0 <= i && i <= n - 1,
                n <= 100000,
                u_edges.len() == n - 1,
                v_edges.len() == n - 1,
                degrees.len() == n + 1,
                forall|k: int| 0 <= k && k <= n ==> 0 <= degrees@[k] && degrees@[k] <= i * 2,
                forall|k: int| 0 <= k && k <= n ==> degrees@[k] as int == count_occ(u_edges@, v_edges@, k as usize, i as int),
                forall|k: int| 0 <= k && k < n - 1 ==> 1 <= u_edges@[k] && u_edges@[k] <= n,
                forall|k: int| 0 <= k && k < n - 1 ==> 1 <= v_edges@[k] && v_edges@[k] <= n,
            decreases n - 1 - i
        {
            let u = u_edges[i];
            let v = v_edges[i];
            
            let old_degrees = degrees.clone();
            
            degrees.set(u, degrees[u] + 1);
            degrees.set(v, degrees[v] + 1);
            
            i += 1;
            
            proof {
                assert forall|k: int| 0 <= k && k <= n implies degrees@[k] as int == count_occ(u_edges@, v_edges@, k as usize, i as int) by {
                    let old_count = count_occ(u_edges@, v_edges@, k as usize, i as int - 1);
                    assert(old_degrees@[k] as int == old_count);
                    let u_val = u_edges@[i as int - 1];
                    let v_val = v_edges@[i as int - 1];
                    let add: int = if u_val == k as usize && v_val == k as usize { 2 } else if u_val == k as usize || v_val == k as usize { 1 } else { 0 };
                    
                }
            }
        }

        let mut high_count = 0;
        let mut center = 1;
        i = 1;
        while i <= n
            invariant
                1 <= i && i <= n + 1,
                n <= 100000,
                0 <= high_count && high_count <= i,
                degrees.len() == n + 1,
                u_edges.len() == n - 1,
                v_edges.len() == n - 1,
                forall|k: int| 0 <= k && k <= n ==> degrees@[k] as int == count_occ(u_edges@, v_edges@, k as usize, u_edges.len() as int),
                high_count == spec_count_high_deg(u_edges@, v_edges@, 1, i as int),
                1 <= center && center <= n,
                high_count >= 1 ==> (center < i && degrees[center as int] >= 3),
            decreases n + 1 - i
        {
            if degrees[i] >= 3 {
                high_count += 1;
                center = i;
            }
            i += 1;
        }

        if high_count > 1 {
            (false, 0, Vec::new())
        } else {
            let mut leaves: Vec<usize> = Vec::new();
            i = 1;
            while i <= n
                invariant
                    1 <= i && i <= n + 1,
                    n <= 100000,
                    degrees.len() == n + 1,
                    u_edges.len() == n - 1,
                    v_edges.len() == n - 1,
                    1 <= center && center <= n,
                    forall|k: int| 0 <= k && k <= n ==> degrees@[k] as int == count_occ(u_edges@, v_edges@, k as usize, u_edges.len() as int),
                    forall|k: int| 0 <= k && k < leaves.len() ==> {
                        let l = #[trigger] leaves@[k];
                        1 <= l && l < i && l != center && degrees@[l as int] == 1
                    },
                    forall|v: int| 1 <= v && v < i ==> {
                        (#[trigger] degrees@[v] == 1 && v != center) ==> 
                            (exists|k: int| 0 <= k && k < leaves.len() && #[trigger] leaves@[k] == v as usize)
                    }
                decreases n + 1 - i
            {
                let old_leaves = leaves.clone();
                if degrees[i] == 1 && i != center {
                    leaves.push(i);
                    proof {
                        let new_leaf_idx = leaves.len() - 1;
                        assert(leaves@[new_leaf_idx as int] == i);
                        assert forall|v: int| 1 <= v && v < i && #[trigger] degrees@[v] == 1 && v != center implies (exists|k: int| 0 <= k && k < leaves.len() && #[trigger] leaves@[k] == v as usize) by {
                            let k_old = choose|k: int| 0 <= k && k < old_leaves.len() && #[trigger] old_leaves@[k] == v as usize;
                            assert(leaves@[k_old] == v as usize);
                        }
                    }
                } else {
                    proof {
                        assert forall|v: int| 1 <= v && v < i && #[trigger] degrees@[v] == 1 && v != center implies (exists|k: int| 0 <= k && k < leaves.len() && #[trigger] leaves@[k] == v as usize) by {
                            let k_old = choose|k: int| 0 <= k && k < old_leaves.len() && #[trigger] old_leaves@[k] == v as usize;
                            assert(leaves@[k_old] == v as usize);
                        }
                    }
                }
                i += 1;
            }
            proof {
                assert forall|k: int| 0 <= k && k < leaves@.len() implies 1 <= leaves@[k] && leaves@[k] <= n && leaves@[k] != center && count_occ(u_edges@, v_edges@, leaves@[k] as usize, u_edges.len() as int) == 1 by {
                    assert(degrees@[leaves@[k] as int] == 1);
                }
                assert forall|v: int| 1 <= v && v <= n && #[trigger] count_occ(u_edges@, v_edges@, v as usize, u_edges.len() as int) == 1 && v != center as int implies exists|k: int| 0 <= k && k < leaves@.len() && #[trigger] leaves@[k] == v as usize by {
                    assert(degrees@[v] == count_occ(u_edges@, v_edges@, v as usize, u_edges.len() as int));
                }
                assert(is_valid_leaves(n, u_edges@, v_edges@, center, leaves@));
            }
            (true, center, leaves)
        }
    }
}

}
