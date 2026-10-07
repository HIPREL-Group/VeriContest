use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, raw: Vec<Vec<i32>>) -> (result: (i32, Vec<Vec<i32>>))
    ensures
        2 <= result.0 <= 500,
        1 <= result.1.len() <= 500,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i][0] < result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][1] <= 500,
        forall|i: int| 1 <= i < result.1.len() ==> #[trigger] result.1[i][1] > result.1[i - 1][1],
        forall|i: int| 1 <= i < result.1.len() ==> #[trigger] result.1[i][0] != result.1[i - 1][0],
{
    let n = if n < 2 { 2 } else if n > 500 { 500 } else { n };
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 500 { 500usize } else { raw.len() };
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous_time = 0i32;
    let mut previous_id = 0i32;
    while i < count
        invariant
            2 <= n <= 500, 1 <= count <= 500, 0 <= i <= count, logs.len() == i,
            0 <= previous_id < n,
            0 <= previous_time <= 500 - count as int + i as int,
            i > 0 ==> logs[i - 1][0] == previous_id && logs[i - 1][1] == previous_time,
            forall|j: int| 0 <= j < logs.len() ==> #[trigger] logs[j].len() == 2,
            forall|j: int| 0 <= j < logs.len() ==> 0 <= #[trigger] logs[j][0] < n,
            forall|j: int| 0 <= j < logs.len() ==> 1 <= #[trigger] logs[j][1] <= 500,
            forall|j: int| 1 <= j < logs.len() ==> #[trigger] logs[j][0] != logs[j - 1][0],
            forall|j: int| 1 <= j < logs.len() ==> #[trigger] logs[j][1] > logs[j - 1][1],
        decreases count - i,
    {
        let id = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 0 };
        let t = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut id = if id < 0 { 0 } else if id >= n { n - 1 } else { id };
        if i > 0 && id == previous_id { id = if id + 1 < n { id + 1 } else { 0 }; }
        let upper = 500 - count as i32 + i as i32 + 1;
        let t = if t > upper { upper } else { t };
        let t = if t <= previous_time { previous_time + 1 } else { t };
        let mut row = Vec::new();
        row.push(id);
        row.push(t);
        logs.push(row);
        previous_id = id;
        previous_time = t;
        i += 1;
    }
    (n, logs)
}


pub fn generate_candidate(
    n: i32,
    ids: &Vec<i32>,
    times: &Vec<i32>,
    mutation_kind: u8,
) -> (logs: Vec<Vec<i32>>)
    requires
        2 <= n <= 500,
        1 <= ids.len() <= 500,
        ids.len() == times.len(),
        forall|i: int| 0 <= i < ids.len() ==> 0 <= #[trigger] ids[i] < n,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 500,
        forall|i: int| 1 <= i < times.len() ==> times[i - 1] < #[trigger] times[i],
    ensures
        2 <= n <= 500,
        1 <= logs.len() <= 500,
        forall|i: int| 0 <= i < logs.len() ==> logs[i].len() == 2,
        forall|i: int| 0 <= i < logs.len() ==> 0 <= #[trigger] logs[i][0] < n,
        forall|i: int| 0 <= i < logs.len() ==> 1 <= #[trigger] logs[i][1] <= 500,
        forall|i: int| 1 <= i < logs.len() ==> logs[i - 1][1] < #[trigger] logs[i][1],
{
    let len = ids.len();
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < len
        invariant
            len == ids.len(),
            len == times.len(),
            1 <= len <= 500,
            2 <= n <= 500,
            0 <= k <= len,
            logs.len() == k,
            forall|j: int| 0 <= j < k as int ==> (#[trigger] logs[j]).len() == 2,
            forall|j: int| 0 <= j < k as int ==> 0 <= #[trigger] logs[j][0] < n,
            forall|j: int| 0 <= j < k as int ==> 1 <= #[trigger] logs[j][1] <= 500,
            forall|j: int| 0 <= j < k as int ==> logs[j][1] == times[j],
            forall|j: int| 1 <= j < k as int ==> logs[j - 1][1] < #[trigger] logs[j][1],
            forall|j: int| 0 <= j < ids.len() ==> 0 <= #[trigger] ids[j] < n,
            forall|j: int| 0 <= j < times.len() ==> 1 <= #[trigger] times[j] <= 500,
            forall|j: int| 1 <= j < times.len() ==> times[j - 1] < #[trigger] times[j],
        decreases len - k,
    {
        let id: i32 = if mutation_kind == 1 {
            0i32
        } else if mutation_kind == 2 {
            n - 1
        } else {
            ids[k]
        };

        let mut entry: Vec<i32> = Vec::new();
        entry.push(id);
        entry.push(times[k]);

        assert(entry.len() == 2);
        assert(entry[0] == id);
        assert(entry[1] == times[k as int]);
        assert(0 <= id < n);

        logs.push(entry);

        assert(logs[k as int].len() == 2);
        assert(logs[k as int][0] == id);
        assert(logs[k as int][1] == times[k as int]);

        k = k + 1;
    }

    logs
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

fn random_sorted_unique_times(rng: &mut Rng, len: usize) -> Vec<i32> {
    use std::collections::BTreeSet;
    let mut set = BTreeSet::new();
    while set.len() < len {
        let t = rng.gen_range_i64(1, 500) as i32;
        set.insert(t);
    }
    set.into_iter().collect()
}

fn random_ids(rng: &mut Rng, len: usize, n: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(0, (n - 1) as i64) as i32).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2432);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |n: i32,
                    logs: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        let (n, logs) = generate_test_case(n, logs);
        if *emitted >= count {
            return;
        }
        let key = format!("{:?},{:?}", n, logs);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::hardest_worker(n, logs.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"n": n, "logs": logs}, "output": result})
        )
        .unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i32, Vec<Vec<i32>>)> = vec![
        (10, vec![vec![0, 3], vec![2, 5], vec![0, 9], vec![1, 15]]),
        (26, vec![vec![1, 1], vec![3, 7], vec![2, 12], vec![7, 17]]),
        (2, vec![vec![0, 10], vec![1, 20]]),
    ];
    for (n, logs) in examples {
        emit(n, logs, &mut seen, &mut out, &mut emitted);
    }

    // Boundary cases
    let boundary_cases: Vec<(i32, Vec<i32>, Vec<i32>)> = vec![
        (2, vec![0], vec![1]),                       // min n, min len, min time
        (500, vec![499], vec![500]),                  // max n, max id, max time
        (2, vec![0, 1], vec![1, 2]),                  // min n, two entries
        (500, vec![0; 1], vec![1]),                   // max n, single entry
    ];
    for (n, ids, times) in boundary_cases {
        let logs = generate_candidate(n, &ids, &times, 0);
        emit(n, logs, &mut seen, &mut out, &mut emitted);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    // Random test cases with diverse size classes
    while emitted < count {
        let n: i32 = match rng.gen_range_usize(0, 4) {
            0 => 2,                                        // min boundary
            1 => rng.gen_range_i64(2, 10) as i32,          // tiny
            2 => rng.gen_range_i64(11, 100) as i32,        // medium
            3 => rng.gen_range_i64(101, 499) as i32,       // large
            _ => 500,                                      // max boundary
        };

        let max_len = std::cmp::min(500, 500); // times are in [1,500], at most 500 unique
        let len: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,                                                      // min
            1 => rng.gen_range_usize(1, 5),                              // tiny
            2 => rng.gen_range_usize(6, 50),                             // medium
            3 => rng.gen_range_usize(51, std::cmp::min(200, max_len)),   // large
            _ => std::cmp::min(500, max_len),                            // max
        };

        let times = random_sorted_unique_times(&mut rng, len);
        let ids = random_ids(&mut rng, len, n);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];

        let logs = generate_candidate(n, &ids, &times, mk);
        emit(n, logs, &mut seen, &mut out, &mut emitted);
    }
}
