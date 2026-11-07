use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    types: Vec<i32>,
    indices: Vec<i32>,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<Vec<i32>>))
    requires
        1 <= n <= 10000,
        1 <= types.len() <= 50000,
        types.len() == indices.len(),
        types.len() == values.len(),
        forall|i: int| 0 <= i < types.len() ==> (#[trigger] types[i] == 0 || types[i] == 1),
        forall|i: int| 0 <= i < indices.len() ==> 0 <= #[trigger] indices[i] && indices[i] < n,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] && values[i] <= 100000,
    ensures
        1 <= result.0 <= 10000,
        1 <= result.1.len() <= 50000,
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i].len() == 3,
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1[i][0] == 0 || result.1[i][0] == 1),
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= result.1[i][1] && result.1[i][1] < result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= result.1[i][2] && result.1[i][2] <= 100000,
{
    let mut mt = types;
    let mut mi = indices;
    let mut mv = values;
    let len = mt.len();

    // Mutations on flat arrays before assembly
    if mutation_kind == 1 {
        // Set last value to 0
        let last = len - 1;
        mv.set(last, 0);
    } else if mutation_kind == 2 {
        // Set last value to 100000
        let last = len - 1;
        mv.set(last, 100000);
    } else if mutation_kind == 3 {
        // Flip last query type
        let last = len - 1;
        if mt[last] == 0 {
            mt.set(last, 1);
        } else {
            mt.set(last, 0);
        }
    } else if mutation_kind == 4 {
        // Set last index to 0
        let last = len - 1;
        mi.set(last, 0);
    } else if mutation_kind == 5 {
        // Set first value to 0
        mv.set(0, 0);
    } else if mutation_kind == 6 {
        // Set first index to 0
        mi.set(0, 0);
    } else if mutation_kind == 7 {
        // Flip first query type
        if mt[0] == 0 {
            mt.set(0, 1);
        } else {
            mt.set(0, 0);
        }
    }
    // else: identity (mutation_kind == 0 or any other)

    // Assemble Vec<Vec<i32>> from flat arrays
    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            len == mt.len(),
            len == mi.len(),
            len == mv.len(),
            1 <= len <= 50000,
            0 <= k <= len,
            queries.len() == k,
            forall|j: int| 0 <= j < k as int ==> (#[trigger] queries[j]).len() == 3,
            forall|j: int| 0 <= j < k as int ==> (queries[j][0] == 0 || queries[j][0] == 1),
            forall|j: int| 0 <= j < k as int ==> 0 <= queries[j][1] && queries[j][1] < n,
            forall|j: int| 0 <= j < k as int ==> 0 <= queries[j][2] && queries[j][2] <= 100000,
            forall|j: int| 0 <= j < mt.len() ==> (#[trigger] mt[j] == 0 || mt[j] == 1),
            forall|j: int| 0 <= j < mi.len() ==> 0 <= #[trigger] mi[j] && mi[j] < n,
            forall|j: int| 0 <= j < mv.len() ==> 0 <= #[trigger] mv[j] && mv[j] <= 100000,
        decreases len - k,
    {
        let mut q: Vec<i32> = Vec::new();
        q.push(mt[k]);
        q.push(mi[k]);
        q.push(mv[k]);
        assert(q.len() == 3);
        assert(q[0] == mt[k as int]);
        assert(q[1] == mi[k as int]);
        assert(q[2] == mv[k as int]);
        queries.push(q);
        k += 1;
    }

    (n, queries)
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_flat_queries(
    rng: &mut Rng,
    n: i32,
    num_queries: usize,
) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut types = Vec::with_capacity(num_queries);
    let mut indices = Vec::with_capacity(num_queries);
    let mut values = Vec::with_capacity(num_queries);
    for _ in 0..num_queries {
        types.push(rng.gen_range_i64(0, 1) as i32);
        indices.push(rng.gen_range_i64(0, (n - 1) as i64) as i32);
        values.push(rng.gen_range_i64(0, 100000) as i32);
    }
    (types, indices, values)
}

fn queries_to_vec(queries: &Vec<Vec<i32>>) -> Vec<Vec<i32>> {
    queries.clone()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2718);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |n: i32,
                    queries: &Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{}{:?}", n, queries);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::matrix_sum_queries(n, queries.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"n": n, "queries": queries}, "output": output})
        )
        .unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    {
        let n = 3;
        let queries = vec![
            vec![0, 0, 1],
            vec![1, 2, 2],
            vec![0, 2, 3],
            vec![1, 0, 4],
        ];
        emit(n, &queries, &mut seen, &mut out, &mut emitted);
    }
    {
        let n = 3;
        let queries = vec![
            vec![0, 0, 4],
            vec![0, 1, 2],
            vec![1, 0, 1],
            vec![0, 2, 3],
            vec![1, 2, 1],
        ];
        emit(n, &queries, &mut seen, &mut out, &mut emitted);
    }

    // Size classes for n
    let n_classes: Vec<i32> = vec![1, 2, 3, 5, 10, 50, 100, 500, 1000, 5000, 10000];
    // Size classes for query count
    let q_classes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 500, 1000];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Structured sweep: each n_class × q_class × mutation_kind
    for &n in &n_classes {
        for &qc in &q_classes {
            if emitted >= count {
                break;
            }
            let (types, indices, values) = random_flat_queries(&mut rng, n, qc);
            let mk = mutation_kinds[emitted % mutation_kinds.len()];
            let (rn, rq) = generate_test_case(n, types, indices, values, mk);
            emit(rn, &rq, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutations
    while emitted < count {
        // Pick n from size classes with some randomness
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(1, 5) as i32,          // tiny
            1 => rng.gen_range_i64(1, 50) as i32,         // small
            2 => rng.gen_range_i64(50, 500) as i32,       // medium
            3 => rng.gen_range_i64(500, 5000) as i32,     // large
            _ => rng.gen_range_i64(5000, 10000) as i32,   // max
        };
        let qc = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),               // tiny
            1 => rng.gen_range_usize(1, 50),              // small
            2 => rng.gen_range_usize(50, 500),            // medium
            3 => rng.gen_range_usize(500, 5000),          // large
            _ => rng.gen_range_usize(5000, 50000),        // max
        };
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (types, indices, values) = random_flat_queries(&mut rng, n, qc);
        let (rn, rq) = generate_test_case(n, types, indices, values, mk);
        emit(rn, &rq, &mut seen, &mut out, &mut emitted);
    }
}
