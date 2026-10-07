use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    land_start_time: Vec<i32>,
    land_duration: Vec<i32>,
    water_start_time: Vec<i32>,
    water_duration: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>))
    requires
        1 <= land_start_time.len() <= 100,
        1 <= water_start_time.len() <= 100,
        land_start_time.len() == land_duration.len(),
        water_start_time.len() == water_duration.len(),
        forall|k: int| 0 <= k < land_start_time.len() ==> 1 <= #[trigger] land_start_time[k] <= 1000,
        forall|k: int| 0 <= k < land_duration.len() ==> 1 <= #[trigger] land_duration[k] <= 1000,
        forall|k: int| 0 <= k < water_start_time.len() ==> 1 <= #[trigger] water_start_time[k] <= 1000,
        forall|k: int| 0 <= k < water_duration.len() ==> 1 <= #[trigger] water_duration[k] <= 1000,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.2.len() <= 100,
        result.0.len() == result.1.len(),
        result.2.len() == result.3.len(),
        forall|k: int| 0 <= k < result.0.len() ==> 1 <= #[trigger] result.0[k] <= 1000,
        forall|k: int| 0 <= k < result.1.len() ==> 1 <= #[trigger] result.1[k] <= 1000,
        forall|k: int| 0 <= k < result.2.len() ==> 1 <= #[trigger] result.2[k] <= 1000,
        forall|k: int| 0 <= k < result.3.len() ==> 1 <= #[trigger] result.3[k] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (land_start_time, land_duration, water_start_time, water_duration)
    } else if mutation_kind == 1 && land_start_time[0] < 1000 {
        // nudge first land start time up
        let mut lst = land_start_time;
        lst.set(0, lst[0] + 1);
        (lst, land_duration, water_start_time, water_duration)
    } else if mutation_kind == 2 && land_start_time[0] > 1 {
        // nudge first land start time down
        let mut lst = land_start_time;
        lst.set(0, lst[0] - 1);
        (lst, land_duration, water_start_time, water_duration)
    } else if mutation_kind == 3 {
        // set first land duration to 1 (min boundary)
        let mut ld = land_duration;
        ld.set(0, 1);
        (land_start_time, ld, water_start_time, water_duration)
    } else if mutation_kind == 4 {
        // set first land duration to 1000 (max boundary)
        let mut ld = land_duration;
        ld.set(0, 1000);
        (land_start_time, ld, water_start_time, water_duration)
    } else if mutation_kind == 5 {
        // set first water start time to 1 (min boundary)
        let mut wst = water_start_time;
        wst.set(0, 1);
        (land_start_time, land_duration, wst, water_duration)
    } else if mutation_kind == 6 {
        // set first water start time to 1000 (max boundary)
        let mut wst = water_start_time;
        wst.set(0, 1000);
        (land_start_time, land_duration, wst, water_duration)
    } else if mutation_kind == 7 {
        // set first water duration to 1 (min boundary)
        let mut wd = water_duration;
        wd.set(0, 1);
        (land_start_time, land_duration, water_start_time, wd)
    } else if mutation_kind == 8 {
        // set first water duration to 1000 (max boundary)
        let mut wd = water_duration;
        wd.set(0, 1000);
        (land_start_time, land_duration, water_start_time, wd)
    } else if mutation_kind == 9 && land_start_time.len() >= 2 {
        // swap first two land start times
        let mut lst = land_start_time;
        let tmp = lst[0];
        lst.set(0, lst[1]);
        lst.set(1, tmp);
        (lst, land_duration, water_start_time, water_duration)
    } else if mutation_kind == 10 && water_start_time.len() >= 2 {
        // swap first two water start times
        let mut wst = water_start_time;
        let tmp = wst[0];
        wst.set(0, wst[1]);
        wst.set(1, tmp);
        (land_start_time, land_duration, wst, water_duration)
    } else if mutation_kind == 11 {
        // set all land start times to 1
        let mut lst = land_start_time;
        let mut i: usize = 0;
        while i < lst.len()
            invariant
                0 <= i <= lst.len(),
                lst.len() == land_duration.len(),
                1 <= lst.len() <= 100,
                forall|j: int| 0 <= j < i ==> lst[j] == 1i32,
                forall|j: int| i <= j < lst.len() ==> lst[j] == land_start_time[j],
            decreases lst.len() - i,
        {
            lst.set(i, 1);
            i += 1;
        }
        (lst, land_duration, water_start_time, water_duration)
    } else if mutation_kind == 12 {
        // set all water durations to 1
        let mut wd = water_duration;
        let mut i: usize = 0;
        while i < wd.len()
            invariant
                0 <= i <= wd.len(),
                wd.len() == water_start_time.len(),
                1 <= wd.len() <= 100,
                forall|j: int| 0 <= j < i ==> wd[j] == 1i32,
                forall|j: int| i <= j < wd.len() ==> wd[j] == water_duration[j],
            decreases wd.len() - i,
        {
            wd.set(i, 1);
            i += 1;
        }
        (land_start_time, land_duration, water_start_time, wd)
    } else if mutation_kind == 13 && water_start_time[0] < 1000 {
        // nudge first water start time up
        let mut wst = water_start_time;
        wst.set(0, wst[0] + 1);
        (land_start_time, land_duration, wst, water_duration)
    } else if mutation_kind == 14 && land_duration[0] > 1 {
        // nudge first land duration down
        let mut ld = land_duration;
        ld.set(0, ld[0] - 1);
        (land_start_time, ld, water_start_time, water_duration)
    } else {
        // fallback: identity
        (land_start_time, land_duration, water_start_time, water_duration)
    }
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

fn mutate(
    lst: Vec<i32>, ld: Vec<i32>,
    wst: Vec<i32>, wd: Vec<i32>,
    mk: u8,
) -> (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    generate_test_case(lst, ld, wst, wd, mk)
}

extern crate serde_json;
use serde_json::json;

fn random_vec(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3633);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |lst: Vec<i32>, ld: Vec<i32>, wst: Vec<i32>, wd: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}|{:?}|{:?}|{:?}", lst, ld, wst, wd);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::earliest_finish_time(lst.clone(), ld.clone(), wst.clone(), wd.clone());
        writeln!(out, "{}", json!({
            "input": {
                "landStartTime": lst,
                "landDuration": ld,
                "waterStartTime": wst,
                "waterDuration": wd
            },
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>)> = vec![
        (vec![2, 8], vec![4, 1], vec![6], vec![3]),
        (vec![5], vec![3], vec![1], vec![10]),
    ];

    // Emit examples with identity mutation first
    for (lst, ld, wst, wd) in &examples {
        emit(lst.clone(), ld.clone(), wst.clone(), wd.clone(),
             &mut seen, &mut out, &mut count);
    }

    // Seed inputs for diverse coverage
    let seed_inputs: Vec<(Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>)> = vec![
        // single ride each
        (vec![1], vec![1], vec![1], vec![1]),
        (vec![1000], vec![1000], vec![1000], vec![1000]),
        (vec![1], vec![1000], vec![1000], vec![1]),
        (vec![500], vec![500], vec![500], vec![500]),
        // two rides each
        (vec![1, 1000], vec![1, 1000], vec![1, 1000], vec![1, 1000]),
        (vec![1, 2], vec![1, 2], vec![1, 2], vec![1, 2]),
        // one vs multiple
        (vec![1], vec![1], vec![1, 500, 1000], vec![1, 500, 1000]),
    ];

    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply every mutation to seed inputs
    for (lst, ld, wst, wd) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rl, rdl, rw, rdw) = mutate(lst.clone(), ld.clone(), wst.clone(), wd.clone(), mk);
            emit(rl, rdl, rw, rdw, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations across size classes
    while count < target_count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,                                   // minimal
            1 => rng.gen_range_usize(1, 5),            // tiny
            2 => rng.gen_range_usize(6, 20),           // small
            3 => rng.gen_range_usize(21, 50),          // medium
            _ => rng.gen_range_usize(51, 100),         // large
        };
        let m = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let lst = random_vec(&mut rng, n, 1, 1000);
        let ld = random_vec(&mut rng, n, 1, 1000);
        let wst = random_vec(&mut rng, m, 1, 1000);
        let wd = random_vec(&mut rng, m, 1, 1000);
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (rl, rdl, rw, rdw) = mutate(lst, ld, wst, wd, mk);
        emit(rl, rdl, rw, rdw, &mut seen, &mut out, &mut count);
    }
}
