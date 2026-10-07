use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    mutation_kind: u8,
) -> (result: (usize, Vec<usize>, Vec<usize>))
    requires
        1 <= n && n <= 100000,
    ensures
        1 <= result.0 && result.0 <= 100000,
        result.1.len() == result.0 - 1,
        result.2.len() == result.0 - 1,
        forall|j: int| 0 <= j && j < result.0 - 1 ==> 1 <= result.1@[j] && result.1@[j] <= result.0,
        forall|j: int| 0 <= j && j < result.0 - 1 ==> 1 <= result.2@[j] && result.2@[j] <= result.0,
{
    let mut u_edges: Vec<usize> = Vec::new();
    let mut v_edges: Vec<usize> = Vec::new();

    if mutation_kind == 1 && n >= 2 {
        // Path tree: edges (1,2), (2,3), ..., (n-1,n)
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                n >= 2,
                1 <= n <= 100000,
                u_edges.len() == i,
                v_edges.len() == i,
                forall|j: int| 0 <= j < i as int ==> u_edges@[j] == (j + 1) as usize,
                forall|j: int| 0 <= j < i as int ==> v_edges@[j] == (j + 2) as usize,
            decreases n - 1 - i,
        {
            u_edges.push(i + 1);
            v_edges.push(i + 2);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                1 <= u_edges@[j] && u_edges@[j] <= n by
            {
                assert(u_edges@[j] == (j + 1) as usize);
            };
            assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                1 <= v_edges@[j] && v_edges@[j] <= n by
            {
                assert(v_edges@[j] == (j + 2) as usize);
            };
        }
    } else if mutation_kind == 2 && n >= 2 {
        // Star tree from node n: edges (n,1), (n,2), ..., (n,n-1)
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                n >= 2,
                1 <= n <= 100000,
                u_edges.len() == i,
                v_edges.len() == i,
                forall|j: int| 0 <= j < i as int ==> u_edges@[j] == n,
                forall|j: int| 0 <= j < i as int ==> v_edges@[j] == (j + 1) as usize,
            decreases n - 1 - i,
        {
            u_edges.push(n);
            v_edges.push(i + 1);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                1 <= u_edges@[j] && u_edges@[j] <= n by
            {
                assert(u_edges@[j] == n);
            };
            assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                1 <= v_edges@[j] && v_edges@[j] <= n by
            {
                assert(v_edges@[j] == (j + 1) as usize);
            };
        }
    } else {
        // Default: Star tree from node 1: edges (1,2), (1,3), ..., (1,n)
        if n >= 2 {
            let mut i: usize = 0;
            while i < n - 1
                invariant
                    0 <= i <= n - 1,
                    n >= 2,
                    1 <= n <= 100000,
                    u_edges.len() == i,
                    v_edges.len() == i,
                    forall|j: int| 0 <= j < i as int ==> u_edges@[j] == 1usize,
                    forall|j: int| 0 <= j < i as int ==> v_edges@[j] == (j + 2) as usize,
                decreases n - 1 - i,
            {
                u_edges.push(1);
                v_edges.push(i + 2);
                i += 1;
            }
            proof {
                assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                    1 <= u_edges@[j] && u_edges@[j] <= n by
                {
                    assert(u_edges@[j] == 1usize);
                };
                assert forall|j: int| 0 <= j && j < (n - 1) as int implies
                    1 <= v_edges@[j] && v_edges@[j] <= n by
                {
                    assert(v_edges@[j] == (j + 2) as usize);
                };
            }
        }
    }

    (n, u_edges, v_edges)
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    let mut emit = |n: usize,
                    u_edges: Vec<usize>,
                    v_edges: Vec<usize>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    generated: &mut usize| {
        if *generated >= count {
            return;
        }
        let key = format!("{}:{:?}:{:?}", n, u_edges, v_edges);
        if !seen.insert(key) {
            return;
        }
        let (has_ans, center, leaves) = Solution::useful_decomposition(n, u_edges.clone(), v_edges.clone());
        writeln!(
            out,
            "{}",
            json!({
                "input": {"n": n, "u_edges": u_edges, "v_edges": v_edges},
                "output": {"has_solution": has_ans, "center": center, "leaves": leaves}
            })
        )
        .unwrap();
        *generated += 1;
    };

    // Example 1: n=4, path 1-2-3-4
    emit(4, vec![1, 2, 3], vec![2, 3, 4], &mut seen, &mut out, &mut generated);
    // Example 2: n=6, two high-degree nodes → No
    emit(6, vec![1, 2, 3, 2, 3], vec![2, 3, 4, 5, 6], &mut seen, &mut out, &mut generated);
    // Example 3: n=5, star from 1
    emit(5, vec![1, 1, 1, 1], vec![2, 3, 4, 5], &mut seen, &mut out, &mut generated);

    // Boundary: n=1, no edges
    emit(1, vec![], vec![], &mut seen, &mut out, &mut generated);
    // Boundary: n=2
    emit(2, vec![1], vec![2], &mut seen, &mut out, &mut generated);

    // Size classes for n
    let n_classes: Vec<(usize, usize)> = vec![
        (1, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 500),    // large
        (501, 1000),   // bigger
    ];

    // Generate with verified generator across size classes and mutations
    for &(lo, hi) in &n_classes {
        for mk in 0..=2u8 {
            if generated >= count {
                break;
            }
            let n = rng.gen_range_usize(lo, hi);
            let (n_out, u_edges, v_edges) = generate_test_case(n, mk);
            emit(n_out, u_edges, v_edges, &mut seen, &mut out, &mut generated);
        }
    }

    // Fill remaining with random parameters
    while generated < count {
        let class = rng.gen_range_usize(0, 4);
        let (lo, hi) = n_classes[class];
        let n = rng.gen_range_usize(lo, hi);
        let mk = rng.gen_u8() % 3;
        let (n_out, u_edges, v_edges) = generate_test_case(n, mk);
        emit(n_out, u_edges, v_edges, &mut seen, &mut out, &mut generated);
    }
}
