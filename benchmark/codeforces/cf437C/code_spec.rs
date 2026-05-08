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
        while i < edges.len() {
            let u = edges[i].0;
            let v = edges[i].1;
            let wu = weights[u];
            let wv = weights[v];
            let add = if wu <= wv { wu } else { wv };
            total += add;
            i += 1;
        }
        total
    }
}

}
