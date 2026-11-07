use vstd::prelude::*;
verus! {
pub fn generate_test_case(births: Vec<i32>, gaps: Vec<i32>, mutation_kind: u8)
    -> (result: Vec<Vec<i32>>)
    requires
        1 <= births.len() <= 100,
        gaps.len() == births.len(),
        forall|i: int| 0 <= i < births.len() ==> 1950 <= #[trigger] births[i] <= 2049,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int|
            0 <= i < result.len() ==> (#[trigger] result[i].len() == 2 && 1950 <= result[i][0]
                && result[i][0] < result[i][1] && result[i][1] <= 2050),
{
    let n = births.len();
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == births.len(), gaps.len() == n, 1 <= n <= 100,
            0 <= idx <= n, logs.len() == idx,
            forall|i: int| 0 <= i < births.len() ==> 1950 <= #[trigger] births[i] <= 2049,
            forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 100,
            forall|j: int| 0 <= j < idx as int ==> (#[trigger] logs[j].len() == 2
                && 1950 <= logs[j][0] && logs[j][0] < logs[j][1] && logs[j][1] <= 2050),
        decreases n - idx,
    {
        let birth = births[idx];
        let gap = gaps[idx];
        let death_raw: i32 = birth + gap;
        let death: i32 = if death_raw > 2050 { 2050i32 } else { death_raw };
        assert(death > birth);
        assert(death <= 2050);
        let mut entry: Vec<i32> = Vec::new();
        entry.push(birth);
        entry.push(death);
        assert(entry.len() == 2);
        assert(entry[0] == birth);
        assert(entry[1] == death);
        logs.push(entry);
        idx += 1;
    }
    if mutation_kind == 1 && logs.len() > 1 {
        logs.pop();
    } else if mutation_kind == 2 && logs.len() < 100 {
        let mut extra: Vec<i32> = Vec::new();
        extra.push(1950i32);
        extra.push(1951i32);
        assert(extra.len() == 2);
        assert(extra[0] == 1950);
        assert(extra[1] == 1951);
        logs.push(extra);
    } else if mutation_kind == 3 {
        let mut e: Vec<i32> = Vec::new();
        e.push(2049i32);
        e.push(2050i32);
        assert(e.len() == 2 && e[0] == 2049 && e[1] == 2050);
        logs.set(0, e);
    } else if mutation_kind == 4 {
        let mut e: Vec<i32> = Vec::new();
        e.push(1950i32);
        e.push(2050i32);
        assert(e.len() == 2 && e[0] == 1950 && e[1] == 2050);
        logs.set(0, e);
    } else if mutation_kind == 5 {
        let mut e: Vec<i32> = Vec::new();
        e.push(2000i32);
        e.push(2025i32);
        assert(e.len() == 2 && e[0] == 2000 && e[1] == 2025);
        logs.set(0, e);
    } else if mutation_kind == 6 {
        let mut e: Vec<i32> = Vec::new();
        e.push(1950i32);
        e.push(1951i32);
        assert(e.len() == 2 && e[0] == 1950 && e[1] == 1951);
        logs.set(0, e);
    }
    proof {
        assert forall|j: int| 0 <= j < logs.len() implies
            (#[trigger] logs[j].len() == 2 && 1950 <= logs[j][0]
                && logs[j][0] < logs[j][1] && logs[j][1] <= 2050)
        by {
            if j == 0 {} else {}
        }
    }
    logs
}
} // verus!
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}
struct Solution;
include!("../code.rs");
fn build_logs(b: Vec<i32>, g: Vec<i32>, mk: u8) -> Vec<Vec<i32>> {
    generate_test_case(b, g, mk)
}
fn rand_bg(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut b = Vec::with_capacity(n);
    let mut g = Vec::with_capacity(n);
    for _ in 0..n {
        b.push(rng.gen_range_i64(1950, 2049) as i32);
        g.push(rng.gen_range_i64(1, 100) as i32);
    }
    (b, g)
}
extern crate serde_json;
use serde_json::json;
fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1854);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let mut emit = |logs: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", logs);
        if !seen.insert(key) { return; }
        let o = Solution::maximum_population(logs.clone());
        writeln!(out, "{}", json!({"input": {"logs": logs}, "output": o})).unwrap();
        *count += 1;
    };
    emit(vec![vec![1993,1999],vec![2000,2010]], &mut seen, &mut out, &mut count);
    emit(vec![vec![1950,1961],vec![1960,1971],vec![1970,1981]], &mut seen, &mut out, &mut count);
    let crafted: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1950], vec![100]), (vec![1950], vec![1]), (vec![2049], vec![1]),
        (vec![1950,1950], vec![1,1]),
        (vec![1950,1950,1950], vec![100,100,100]),
        (vec![1950,1960,1970,1980,1990], vec![10,10,10,10,10]),
        (vec![2000,2000,2000,2000,2000], vec![1,1,1,1,1]),
        (vec![1950,1975], vec![50,75]),
        (vec![1950], vec![50]),
        (vec![2000,2010,2020], vec![20,20,20]),
    ];
    for (b, g) in &crafted {
        for mk in 0u8..=6 {
            emit(build_logs(b.clone(), g.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }
    let sc: Vec<(usize,usize)> = vec![(1,1),(2,3),(4,10),(11,30),(31,60),(61,100)];
    for &(lo, hi) in &sc {
        for _ in 0..5 {
            if count >= target { break; }
            let n = rng.gen_range_usize(lo, hi);
            let (b, g) = rand_bg(&mut rng, n);
            let mk = rng.gen_range_usize(0, 6) as u8;
            emit(build_logs(b, g, mk), &mut seen, &mut out, &mut count);
        }
    }
    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let (b, g) = rand_bg(&mut rng, n);
        let mk = rng.gen_range_usize(0, 6) as u8;
        emit(build_logs(b, g, mk), &mut seen, &mut out, &mut count);
    }
}
