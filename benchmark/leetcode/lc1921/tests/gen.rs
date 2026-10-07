use vstd::prelude::*;

verus! {

pub fn generate_test_case(dist: Vec<i32>, speed: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, Vec<i32>))
    requires
        dist.len() == speed.len(),
        1 <= dist.len() <= 100_000,
        forall|i: int| 0 <= i < dist.len() ==> 1 <= #[trigger] dist[i] <= 100_000,
        forall|i: int| 0 <= i < speed.len() ==> 1 <= #[trigger] speed[i] <= 100_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (dist, speed)
    } else if mutation_kind == 1 {
        // set all dist values to 1 (minimum boundary)
        let mut d = dist;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == dist.len(),
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == dist[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, speed)
    } else if mutation_kind == 2 {
        // set all speed values to 1 (minimum boundary)
        let mut s = speed;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == speed.len(),
                forall|j: int| 0 <= j < i ==> s[j] == 1i32,
                forall|j: int| i <= j < s.len() ==> s[j] == speed[j],
            decreases s.len() - i,
        {
            s.set(i, 1);
            i += 1;
        }
        (dist, s)
    } else if mutation_kind == 3 {
        // set all dist values to 100_000 (maximum boundary)
        let mut d = dist;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == dist.len(),
                forall|j: int| 0 <= j < i ==> d[j] == 100_000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == dist[j],
            decreases d.len() - i,
        {
            d.set(i, 100_000);
            i += 1;
        }
        (d, speed)
    } else if mutation_kind == 4 {
        // set all speed values to 100_000 (maximum boundary)
        let mut s = speed;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == speed.len(),
                forall|j: int| 0 <= j < i ==> s[j] == 100_000i32,
                forall|j: int| i <= j < s.len() ==> s[j] == speed[j],
            decreases s.len() - i,
        {
            s.set(i, 100_000);
            i += 1;
        }
        (dist, s)
    } else if mutation_kind == 5 && dist[0] < 100_000 {
        // nudge first dist element up
        let mut d = dist;
        d.set(0, d[0] + 1);
        (d, speed)
    } else if mutation_kind == 6 && speed[0] < 100_000 {
        // nudge first speed element up
        let mut s = speed;
        s.set(0, s[0] + 1);
        (dist, s)
    } else if mutation_kind == 7 && dist[0] > 1 {
        // nudge first dist element down
        let mut d = dist;
        d.set(0, d[0] - 1);
        (d, speed)
    } else if mutation_kind == 8 && speed[0] > 1 {
        // nudge first speed element down
        let mut s = speed;
        s.set(0, s[0] - 1);
        (dist, s)
    } else if mutation_kind == 9 && dist.len() >= 2 {
        // swap first two elements of dist
        let mut d = dist;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, speed)
    } else if mutation_kind == 10 && dist.len() >= 2 {
        // swap first two elements of speed
        let mut s = speed;
        let tmp = s[0];
        s.set(0, s[1]);
        s.set(1, tmp);
        (dist, s)
    } else if mutation_kind == 11 && dist.len() < 100_000 {
        // grow both arrays by one element (push 1)
        let mut d = dist;
        let mut s = speed;
        d.push(1);
        s.push(1);
        (d, s)
    } else if mutation_kind == 12 && dist.len() > 1 {
        // shrink both arrays by one element (pop)
        let mut d = dist;
        let mut s = speed;
        d.pop();
        s.pop();
        (d, s)
    } else {
        // fallback: identity
        (dist, speed)
    }
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

fn random_pair(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut dist = Vec::with_capacity(len);
    let mut speed = Vec::with_capacity(len);
    for _ in 0..len {
        dist.push(rng.gen_range_i64(1, 100_000) as i32);
        speed.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    (dist, speed)
}

fn mutate(dist: Vec<i32>, speed: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(dist, speed, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1921);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |dist: Vec<i32>, speed: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", dist, speed);
        if !seen.insert(key) { return; }
        let output = Solution::eliminate_maximum(dist.clone(), speed.clone());
        writeln!(out, "{}", json!({
            "input": {"dist": dist, "speed": speed},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 3, 4], vec![1, 1, 1], &mut seen, &mut out, &mut emitted);
    emit(vec![1, 1, 2, 3], vec![1, 1, 1, 1], &mut seen, &mut out, &mut emitted);
    emit(vec![3, 2, 4], vec![5, 3, 2], &mut seen, &mut out, &mut emitted);

    // Boundary: single element
    emit(vec![1], vec![1], &mut seen, &mut out, &mut emitted);
    emit(vec![100_000], vec![100_000], &mut seen, &mut out, &mut emitted);
    emit(vec![1], vec![100_000], &mut seen, &mut out, &mut emitted);
    emit(vec![100_000], vec![1], &mut seen, &mut out, &mut emitted);

    // Boundary: all same values
    emit(vec![1, 1], vec![1, 1], &mut seen, &mut out, &mut emitted);
    emit(vec![2, 2, 2], vec![1, 1, 1], &mut seen, &mut out, &mut emitted);

    // Seed pool: interesting small cases with mutations
    let seed_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 3, 4], vec![1, 1, 1]),
        (vec![1, 1, 2, 3], vec![1, 1, 1, 1]),
        (vec![3, 2, 4], vec![5, 3, 2]),
        (vec![5, 10, 15, 20], vec![1, 2, 3, 4]),
        (vec![1, 2], vec![1, 1]),
        (vec![100_000], vec![1]),
        (vec![2, 3, 4, 5, 6], vec![1, 1, 1, 1, 1]),
    ];

    for (d, s) in &seed_cases {
        for mk in 0..=12u8 {
            if emitted >= count { break; }
            let (md, ms) = mutate(d.clone(), s.clone(), mk);
            emit(md, ms, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random generation across size classes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),           // tiny
            1 => rng.gen_range_usize(1, 10),           // small
            2 => rng.gen_range_usize(11, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            _ => rng.gen_range_usize(1001, 10_000),    // very large
        };

        let (d, s) = random_pair(&mut rng, n);
        let mk = (rng.next_u64() % 13) as u8;
        let (md, ms) = mutate(d, s, mk);
        emit(md, ms, &mut seen, &mut out, &mut emitted);
    }
}
