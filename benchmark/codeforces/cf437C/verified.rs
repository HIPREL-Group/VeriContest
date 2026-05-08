use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn same_undirected_edge(a: (usize, usize), b: (usize, usize)) -> bool {
    (a.0 == b.0 && a.1 == b.1) || (a.0 == b.1 && a.1 == b.0)
}

pub open spec fn valid_edge(weights: Seq<i64>, edge: (usize, usize)) -> bool {
    edge.0 < weights.len() && edge.1 < weights.len() && edge.0 != edge.1
}

pub open spec fn edge_energy(weights: Seq<i64>, edge: (usize, usize)) -> int {
    if valid_edge(weights, edge) {
        let wu = weights[edge.0 as int] as int;
        let wv = weights[edge.1 as int] as int;
        if wu <= wv { wu } else { wv }
    } else {
        0
    }
}

pub open spec fn total_energy_prefix(weights: Seq<i64>, edges: Seq<(usize, usize)>, end: nat) -> int
    recommends
        end <= edges.len(),
    decreases end,
{
    if end == 0 {
        0
    } else {
        total_energy_prefix(weights, edges, (end - 1) as nat) + edge_energy(weights, edges[end as int - 1])
    }
}

pub open spec fn total_energy(weights: Seq<i64>, edges: Seq<(usize, usize)>) -> int {
    total_energy_prefix(weights, edges, edges.len())
}

proof fn lemma_edge_energy_bound(weights: Seq<i64>, edge: (usize, usize))
    requires
        forall|i: int| 0 <= i < weights.len() ==> 0 <= #[trigger] weights[i] && weights[i] <= 100_000,
        valid_edge(weights, edge),
    ensures
        0 <= edge_energy(weights, edge) <= 100_000,
{
    assert(0 <= weights[edge.0 as int] && weights[edge.0 as int] <= 100_000);
    assert(0 <= weights[edge.1 as int] && weights[edge.1 as int] <= 100_000);
}

proof fn lemma_total_energy_prefix_bound(weights: Seq<i64>, edges: Seq<(usize, usize)>, end: nat)
    requires
        forall|i: int| 0 <= i < weights.len() ==> 0 <= #[trigger] weights[i] && weights[i] <= 100_000,
        forall|k: int| 0 <= k < edges.len() ==> #[trigger] valid_edge(weights, edges[k]),
        end <= edges.len(),
    ensures
        0 <= total_energy_prefix(weights, edges, end) <= 100_000 * end as int,
    decreases end,
{
    if end != 0 {
        lemma_total_energy_prefix_bound(weights, edges, (end - 1) as nat);
        lemma_edge_energy_bound(weights, edges[end as int - 1]);
        assert(total_energy_prefix(weights, edges, end) == total_energy_prefix(weights, edges, (end - 1) as nat) + edge_energy(weights, edges[end as int - 1]));
    }
}

impl Solution {
    pub fn min_total_energy(weights: Vec<i64>, edges: Vec<(usize, usize)>) -> (res: i64)
        requires
            1 <= weights.len() <= 1000,
            0 <= edges.len() <= 2000,
            forall|i: int| 0 <= i < weights.len() ==> 0 <= #[trigger] weights@[i] && weights@[i] <= 100_000,
            forall|k: int| 0 <= k < edges.len() ==> #[trigger] valid_edge(weights@, edges@[k]),
            forall|i: int, j: int|
                0 <= i < j < edges.len() ==> !same_undirected_edge(edges@[i], edges@[j]),
        ensures
            res as int == total_energy(weights@, edges@),
    {
        let mut total = 0i64;
        let mut i = 0usize;
        while i < edges.len()
            invariant
                0 <= i <= edges.len(),
                edges.len() <= 2000,
                forall|j: int| 0 <= j < weights.len() ==> 0 <= #[trigger] weights@[j] && weights@[j] <= 100_000,
                forall|k: int| 0 <= k < edges.len() ==> #[trigger] valid_edge(weights@, edges@[k]),
                total as int == total_energy_prefix(weights@, edges@, i as nat),
                0 <= total as int <= 100_000 * i as int,
            decreases edges.len() - i,
        {
            let u = edges[i].0;
            let v = edges[i].1;
            proof {
                assert(valid_edge(weights@, edges@[i as int]));
                assert(edges@[i as int].0 == u);
                assert(edges@[i as int].1 == v);
                assert(u < weights.len());
                assert(v < weights.len());
            }
            let wu = weights[u];
            let wv = weights[v];
            let add = if wu <= wv { wu } else { wv };
            proof {
                lemma_edge_energy_bound(weights@, edges@[i as int]);
                assert(weights@[u as int] == wu);
                assert(weights@[v as int] == wv);
                if wu <= wv {
                    assert(add == wu);
                    assert(edge_energy(weights@, edges@[i as int]) == weights@[u as int] as int);
                } else {
                    assert(add == wv);
                    assert(edge_energy(weights@, edges@[i as int]) == weights@[v as int] as int);
                }
                assert(add as int == edge_energy(weights@, edges@[i as int]));
                assert(total_energy_prefix(weights@, edges@, (i + 1) as nat) == total_energy_prefix(weights@, edges@, i as nat) + edge_energy(weights@, edges@[i as int]));
                assert(total as int + add as int == total_energy_prefix(weights@, edges@, (i + 1) as nat));
                assert((i as int) < edges.len() as int);
                assert(100_000 * ((i as int) + 1) <= 100_000 * edges.len() as int);
                assert(edges.len() <= 2000);
                assert(edges.len() as int <= 2000);
                assert(100_000 * edges.len() as int <= 100_000 * 2000);
                assert(100_000 * edges.len() as int <= 200_000_000);
                assert(0 <= total as int + add as int <= 200_000_000);
            }
            total += add;
            i += 1;
        }
        proof {
            assert(i == edges.len());
            assert(total as int == total_energy_prefix(weights@, edges@, edges.len() as nat));
            assert(total_energy(weights@, edges@) == total_energy_prefix(weights@, edges@, edges.len() as nat));
        }
        total
    }
}

}
