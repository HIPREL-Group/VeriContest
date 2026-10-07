use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: i32,
    cols: i32,
    hcuts: Vec<i32>,
    vcuts: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= rows <= 20,
        1 <= cols <= 20,
        hcuts.len() == rows - 1,
        vcuts.len() == cols - 1,
        forall|i: int| 0 <= i < hcuts.len() ==> 1 <= #[trigger] hcuts[i] <= 1000,
        forall|j: int| 0 <= j < vcuts.len() ==> 1 <= #[trigger] vcuts[j] <= 1000,
    ensures
        1 <= result.0 <= 20,
        1 <= result.1 <= 20,
        result.2.len() == result.0 - 1,
        result.3.len() == result.1 - 1,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 1000,
        forall|j: int| 0 <= j < result.3.len() ==> 1 <= #[trigger] result.3[j] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (rows, cols, hcuts, vcuts)
    } else if mutation_kind == 1 {
        // set all horizontal cuts to 1 (minimum cost)
        let mut hcut = hcuts;
        let mut i: usize = 0;
        while i < hcut.len()
            invariant
                0 <= i <= hcut.len(),
                hcut.len() == hcuts.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] hcut[k] == 1,
                forall|k: int| i <= k < hcut.len() ==> #[trigger] hcut[k] == hcuts[k],
            decreases hcut.len() - i,
        {
            hcut.set(i, 1);
            i += 1;
        }
        (rows, cols, hcut, vcuts)
    } else if mutation_kind == 2 {
        // set all vertical cuts to 1 (minimum cost)
        let mut vcut = vcuts;
        let mut j: usize = 0;
        while j < vcut.len()
            invariant
                0 <= j <= vcut.len(),
                vcut.len() == vcuts.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] vcut[k] == 1,
                forall|k: int| j <= k < vcut.len() ==> #[trigger] vcut[k] == vcuts[k],
            decreases vcut.len() - j,
        {
            vcut.set(j, 1);
            j += 1;
        }
        (rows, cols, hcuts, vcut)
    } else if mutation_kind == 3 {
        // set all horizontal cuts to 1000 (maximum cost)
        let mut hcut = hcuts;
        let mut i: usize = 0;
        while i < hcut.len()
            invariant
                0 <= i <= hcut.len(),
                hcut.len() == hcuts.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] hcut[k] == 1000,
                forall|k: int| i <= k < hcut.len() ==> #[trigger] hcut[k] == hcuts[k],
            decreases hcut.len() - i,
        {
            hcut.set(i, 1000);
            i += 1;
        }
        (rows, cols, hcut, vcuts)
    } else if mutation_kind == 4 {
        // set all vertical cuts to 1000 (maximum cost)
        let mut vcut = vcuts;
        let mut j: usize = 0;
        while j < vcut.len()
            invariant
                0 <= j <= vcut.len(),
                vcut.len() == vcuts.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] vcut[k] == 1000,
                forall|k: int| j <= k < vcut.len() ==> #[trigger] vcut[k] == vcuts[k],
            decreases vcut.len() - j,
        {
            vcut.set(j, 1000);
            j += 1;
        }
        (rows, cols, hcuts, vcut)
    } else if mutation_kind == 5 && hcuts.len() > 0 {
        // nudge first horizontal cut up
        let mut hcut = hcuts;
        if hcut[0] < 1000 {
            hcut.set(0, hcut[0] + 1);
        }
        (rows, cols, hcut, vcuts)
    } else if mutation_kind == 6 && vcuts.len() > 0 {
        // nudge first vertical cut up
        let mut vcut = vcuts;
        if vcut[0] < 1000 {
            vcut.set(0, vcut[0] + 1);
        }
        (rows, cols, hcuts, vcut)
    } else if mutation_kind == 7 && hcuts.len() > 0 {
        // nudge first horizontal cut down
        let mut hcut = hcuts;
        if hcut[0] > 1 {
            hcut.set(0, hcut[0] - 1);
        }
        (rows, cols, hcut, vcuts)
    } else if mutation_kind == 8 && vcuts.len() > 0 {
        // nudge first vertical cut down
        let mut vcut = vcuts;
        if vcut[0] > 1 {
            vcut.set(0, vcut[0] - 1);
        }
        (rows, cols, hcuts, vcut)
    } else if mutation_kind == 9 && hcuts.len() >= 2 {
        // swap first two horizontal cuts
        let mut hcut = hcuts;
        let tmp = hcut[0];
        hcut.set(0, hcut[1]);
        hcut.set(1, tmp);
        (rows, cols, hcut, vcuts)
    } else if mutation_kind == 10 && vcuts.len() >= 2 {
        // swap first two vertical cuts
        let mut vcut = vcuts;
        let tmp = vcut[0];
        vcut.set(0, vcut[1]);
        vcut.set(1, tmp);
        (rows, cols, hcuts, vcut)
    } else if mutation_kind == 11 {
        // set all cuts to 500
        let mut hcut = hcuts;
        let mut i: usize = 0;
        while i < hcut.len()
            invariant
                0 <= i <= hcut.len(),
                hcut.len() == hcuts.len(),
                forall|k: int| 0 <= k < i ==> #[trigger] hcut[k] == 500,
                forall|k: int| i <= k < hcut.len() ==> #[trigger] hcut[k] == hcuts[k],
            decreases hcut.len() - i,
        {
            hcut.set(i, 500);
            i += 1;
        }
        let mut vcut = vcuts;
        let mut j: usize = 0;
        while j < vcut.len()
            invariant
                0 <= j <= vcut.len(),
                vcut.len() == vcuts.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] vcut[k] == 500,
                forall|k: int| j <= k < vcut.len() ==> #[trigger] vcut[k] == vcuts[k],
            decreases vcut.len() - j,
        {
            vcut.set(j, 500);
            j += 1;
        }
        (rows, cols, hcut, vcut)
    } else {
        // fallback: identity
        (rows, cols, hcuts, vcuts)
    }
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

fn random_cuts(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cuts = Vec::with_capacity(len);
    for _ in 0..len {
        cuts.push(rng.gen_range_i64(1, 1000) as i32);
    }
    cuts
}

fn mutate(
    m: i32,
    n: i32,
    hcuts: Vec<i32>,
    vcuts: Vec<i32>,
    mutation_kind: u8,
) -> (i32, i32, Vec<i32>, Vec<i32>) {
    generate_test_case(m, n, hcuts, vcuts, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3218);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |m: i32, n: i32, hcut: Vec<i32>, vcut: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{},{},{:?},{:?}", m, n, hcut, vcut);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_cost(m, n, hcut.clone(), vcut.clone());
        writeln!(out, "{}", json!({
            "input": {"m": m, "n": n, "horizontalCut": hcut, "verticalCut": vcut},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    emit(3, 2, vec![1, 3], vec![5], &mut seen, &mut out, &mut total);
    emit(2, 2, vec![7], vec![4], &mut seen, &mut out, &mut total);

    // Boundary: m=1 or n=1 (empty cut arrays)
    emit(1, 1, vec![], vec![], &mut seen, &mut out, &mut total);
    emit(1, 5, vec![], vec![1, 2, 3, 4], &mut seen, &mut out, &mut total);
    emit(5, 1, vec![1, 2, 3, 4], vec![], &mut seen, &mut out, &mut total);

    // Max size: m=20, n=20
    emit(20, 20, random_cuts(&mut rng, 19), random_cuts(&mut rng, 19),
         &mut seen, &mut out, &mut total);

    // Structured seeds with all mutation kinds
    let seed_configs: Vec<(i32, i32)> = vec![
        (2, 2), (3, 3), (5, 5), (10, 10), (20, 20),
        (1, 20), (20, 1), (2, 20), (20, 2),
        (3, 2), (2, 3), (4, 4),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    for &(m, n) in &seed_configs {
        let hcut = random_cuts(&mut rng, (m - 1) as usize);
        let vcut = random_cuts(&mut rng, (n - 1) as usize);
        for &mk in &mutation_kinds {
            let (rm, rn, rh, rv) = mutate(m, n, hcut.clone(), vcut.clone(), mk);
            emit(rm, rn, rh, rv, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with random mutations across diverse size classes
    while total < count {
        let m: i32 = match total % 5 {
            0 => rng.gen_range_i64(1, 2) as i32,      // tiny
            1 => rng.gen_range_i64(1, 5) as i32,      // small
            2 => rng.gen_range_i64(5, 10) as i32,     // medium
            3 => rng.gen_range_i64(10, 15) as i32,    // large
            _ => rng.gen_range_i64(15, 20) as i32,    // max
        };
        let n: i32 = match total % 7 {
            0 => rng.gen_range_i64(1, 2) as i32,
            1 => rng.gen_range_i64(1, 5) as i32,
            2 => rng.gen_range_i64(5, 10) as i32,
            3 => rng.gen_range_i64(10, 15) as i32,
            4 => rng.gen_range_i64(15, 20) as i32,
            5 => 1,
            _ => 20,
        };
        let hcut = random_cuts(&mut rng, (m - 1) as usize);
        let vcut = random_cuts(&mut rng, (n - 1) as usize);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (rm, rn, rh, rv) = mutate(m, n, hcut, vcut, mk);
        emit(rm, rn, rh, rv, &mut seen, &mut out, &mut total);
    }
}
