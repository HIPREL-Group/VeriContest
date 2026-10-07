use vstd::prelude::*;

verus! {

/// Constructs a valid `(Vec<Vec<i32>>, i32)` representing `(requests, n)` for
/// Maximum Number of Achievable Transfer Requests (LC 1601).
///
/// Construction parameters are parallel arrays of `froms` and `tos` (each
/// value in `[0, n)`), plus `n` and `mutation_kind` for diversity.
pub fn generate_test_case(
    froms: &Vec<i32>,
    tos: &Vec<i32>,
    n: i32,
    mutation_kind: u8,
) -> (result: (i32, Vec<Vec<i32>>))
    requires
        1 <= n <= 20,
        1 <= froms.len() <= 16,
        froms.len() == tos.len(),
        forall|i: int| 0 <= i < froms.len() ==> 0 <= #[trigger] froms[i] < n,
        forall|i: int| 0 <= i < tos.len() ==> 0 <= #[trigger] tos[i] < n,
    ensures
        1 <= result.0 <= 20,
        1 <= result.1.len() <= 16,
        forall|i: int| 0 <= i < result.1.len() ==>
            #[trigger] result.1[i].len() == 2
            && 0 <= result.1[i][0] < result.0
            && 0 <= result.1[i][1] < result.0,
{
    let mut requests: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    // Mutation strategies:
    // 0 - normal (use froms/tos as-is)
    // 1 - self-loops: to = from for every request
    // 2 - all from building 0
    // 3 - all to building 0
    // 4 - swap from/to
    // 5 - all requests identical: from=0, to=0

    while k < froms.len()
        invariant
            0 <= k <= froms.len(),
            1 <= n <= 20,
            froms.len() == tos.len(),
            1 <= froms.len() <= 16,
            requests.len() == k,
            forall|i: int| 0 <= i < froms.len() ==> 0 <= #[trigger] froms[i] < n,
            forall|i: int| 0 <= i < tos.len() ==> 0 <= #[trigger] tos[i] < n,
            forall|j: int| 0 <= j < k ==> #[trigger] requests[j]@.len() == 2,
            forall|j: int| 0 <= j < k ==>
                0 <= #[trigger] requests[j][0] < n
                && 0 <= requests[j][1] < n,
        decreases froms.len() - k,
    {
        let from_val: i32 = if mutation_kind == 2 || mutation_kind == 5 {
            0i32
        } else if mutation_kind == 4 {
            tos[k]
        } else {
            froms[k]
        };

        let to_val: i32 = if mutation_kind == 1 {
            froms[k]
        } else if mutation_kind == 3 || mutation_kind == 5 {
            0i32
        } else if mutation_kind == 4 {
            froms[k]
        } else {
            tos[k]
        };

        assert(0 <= from_val < n);
        assert(0 <= to_val < n);

        let mut r: Vec<i32> = Vec::new();
        r.push(from_val);
        r.push(to_val);

        assert(r@.len() == 2);
        assert(r[0] == from_val);
        assert(r[1] == to_val);

        requests.push(r);
        k = k + 1;
    }

    (n, requests)
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

fn random_requests(rng: &mut Rng, n: i32, num_requests: usize) -> (Vec<i32>, Vec<i32>) {
    let mut froms = Vec::with_capacity(num_requests);
    let mut tos = Vec::with_capacity(num_requests);
    for _ in 0..num_requests {
        froms.push(rng.gen_range_i64(0, (n - 1) as i64) as i32);
        tos.push(rng.gen_range_i64(0, (n - 1) as i64) as i32);
    }
    (froms, tos)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1601);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |requests_vec: Vec<Vec<i32>>, n: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?},{}", requests_vec, n);
        if !seen.insert(key) { return; }
        let result = Solution::maximum_requests(n, requests_vec.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "requests": requests_vec},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example 1: n = 5, requests = [[0,1],[1,0],[0,1],[1,2],[2,0],[3,4]]
    {
        let froms = vec![0, 1, 0, 1, 2, 3];
        let tos   = vec![1, 0, 1, 2, 0, 4];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 5, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: n = 3, requests = [[0,0],[1,2],[2,1]]
    {
        let froms = vec![0, 1, 2];
        let tos   = vec![0, 2, 1];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 3, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: n = 4, requests = [[0,3],[3,1],[1,2],[2,0]]
    {
        let froms = vec![0, 3, 1, 2];
        let tos   = vec![3, 1, 2, 0];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 4, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single request, single building (self-loop)
    {
        let froms = vec![0];
        let tos   = vec![0];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 1, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: max requests (16), 2 buildings
    {
        let froms = vec![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1];
        let tos   = vec![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 2, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: max buildings (20), single request
    {
        let froms = vec![0];
        let tos   = vec![19];
        for mk in 0u8..=5 {
            let (nn, rq) = generate_test_case(&froms, &tos, 20, mk);
            emit(rq, nn, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];
    while count < target_count {
        // Size class for n
        let n: i32 = match rng.gen_range_usize(0, 4) {
            0 => 1,                                       // min
            1 => rng.gen_range_i64(1, 5) as i32,          // tiny
            2 => rng.gen_range_i64(2, 10) as i32,         // small
            3 => rng.gen_range_i64(5, 15) as i32,         // medium
            _ => rng.gen_range_i64(10, 20) as i32,        // max range
        };

        // Size class for number of requests
        let nr: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                       // min
            1 => rng.gen_range_usize(1, 4),               // tiny
            2 => rng.gen_range_usize(2, 8),               // small
            3 => rng.gen_range_usize(5, 12),              // medium
            _ => rng.gen_range_usize(10, 16),             // max range
        };

        let (froms, tos) = random_requests(&mut rng, n, nr);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (nn, rq) = generate_test_case(&froms, &tos, n, mk);
        emit(rq, nn, &mut seen, &mut out, &mut count);
    }
}
