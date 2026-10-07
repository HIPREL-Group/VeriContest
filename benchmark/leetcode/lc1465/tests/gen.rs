use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    h: i32,
    w: i32,
    num_h: usize,
    num_v: usize,
    h_start: i32,
    v_start: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        2 <= h <= 1_000_000_000,
        2 <= w <= 1_000_000_000,
        1 <= num_h <= 100_000,
        1 <= num_v <= 100_000,
        1 <= h_start,
        h_start as int + num_h as int <= h as int,
        1 <= v_start,
        v_start as int + num_v as int <= w as int,
    ensures
        2 <= result.0 <= 1_000_000_000,
        2 <= result.1 <= 1_000_000_000,
        1 <= result.2.len() <= 100_000,
        1 <= result.3.len() <= 100_000,
        forall |i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] < result.0,
        forall |j: int| 0 <= j < result.3.len() ==> 1 <= #[trigger] result.3[j] < result.1,
        forall |i: int, j: int| 0 <= i < j < result.2.len() ==> result.2[i] != result.2[j],
        forall |i: int, j: int| 0 <= i < j < result.3.len() ==> result.3[i] != result.3[j],
{
    // Build horizontal cuts as ascending consecutive integers from h_start
    let mut h_cuts: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < num_h
        invariant
            0 <= k <= num_h,
            h_cuts.len() == k,
            1 <= num_h <= 100_000,
            1 <= h_start,
            h_start as int + num_h as int <= h as int,
            h as int <= 1_000_000_000,
            forall |i: int| 0 <= i < k as int ==>
                #[trigger] h_cuts[i] as int == h_start as int + i,
        decreases num_h - k,
    {
        let val: i32 = h_start + k as i32;
        h_cuts.push(val);
        k += 1;
    }
    proof {
        assert forall |i: int, j: int| 0 <= i < j < h_cuts.len()
            implies h_cuts[i] != h_cuts[j] by
        {
            assert(h_cuts[i] as int == h_start as int + i);
            assert(h_cuts[j] as int == h_start as int + j);
        }
        assert forall |i: int| 0 <= i < h_cuts.len()
            implies 1 <= #[trigger] h_cuts[i] < h by
        {
            assert(h_cuts[i] as int == h_start as int + i);
        }
    }

    // Build vertical cuts as ascending consecutive integers from v_start
    let mut v_cuts: Vec<i32> = Vec::new();
    let mut m: usize = 0;
    while m < num_v
        invariant
            0 <= m <= num_v,
            v_cuts.len() == m,
            1 <= num_v <= 100_000,
            1 <= v_start,
            v_start as int + num_v as int <= w as int,
            w as int <= 1_000_000_000,
            forall |j: int| 0 <= j < m as int ==>
                #[trigger] v_cuts[j] as int == v_start as int + j,
        decreases num_v - m,
    {
        let val: i32 = v_start + m as i32;
        v_cuts.push(val);
        m += 1;
    }
    proof {
        assert forall |i: int, j: int| 0 <= i < j < v_cuts.len()
            implies v_cuts[i] != v_cuts[j] by
        {
            assert(v_cuts[i] as int == v_start as int + i);
            assert(v_cuts[j] as int == v_start as int + j);
        }
        assert forall |j: int| 0 <= j < v_cuts.len()
            implies 1 <= #[trigger] v_cuts[j] < w by
        {
            assert(v_cuts[j] as int == v_start as int + j);
        }
    }

    (h, w, h_cuts, v_cuts)
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |h: i32, w: i32,
                    horizontal_cuts: Vec<i32>,
                    vertical_cuts: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{},{},{:?},{:?}", h, w, horizontal_cuts, vertical_cuts);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_area(h, w, horizontal_cuts.clone(), vertical_cuts.clone());
        writeln!(out, "{}", json!({
            "input": {
                "h": h,
                "w": w,
                "horizontal_cuts": horizontal_cuts,
                "vertical_cuts": vertical_cuts
            },
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example 1
    emit(5, 4, vec![1,2,4], vec![1,3], &mut seen, &mut out, &mut count);
    // Example 2
    emit(5, 4, vec![3,1], vec![1], &mut seen, &mut out, &mut count);
    // Example 3
    emit(5, 4, vec![3], vec![3], &mut seen, &mut out, &mut count);

    // Size classes for h/w
    let hw_classes: Vec<i32> = vec![
        2, 3, 5, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 1_000_000_000,
    ];

    // Fixed diverse test cases with various sizes
    for &hv in &hw_classes {
        for &wv in &[2i32, 10, 1_000_000_000] {
            if count >= count_target { break; }
            let max_nh = std::cmp::min((hv - 1) as usize, 100_000);
            let max_nv = std::cmp::min((wv - 1) as usize, 100_000);
            for num_h in [1usize, std::cmp::min(3, max_nh), max_nh] {
                if num_h < 1 || num_h > max_nh { continue; }
                let num_v = std::cmp::min(3, max_nv).max(1);
                let h_start = 1i32;
                let v_start = 1i32;
                let (rh, rw, hc, vc) = generate_test_case(hv, wv, num_h, num_v, h_start, v_start, 0);
                emit(rh, rw, hc, vc, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with diverse parameter sampling
    while count < count_target {
        let h: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(2, 5) as i32,
            1 => rng.gen_range_i64(6, 100) as i32,
            2 => rng.gen_range_i64(101, 100_000) as i32,
            3 => rng.gen_range_i64(100_001, 1_000_000) as i32,
            _ => rng.gen_range_i64(1_000_001, 1_000_000_000) as i32,
        };
        let w: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(2, 5) as i32,
            1 => rng.gen_range_i64(6, 100) as i32,
            2 => rng.gen_range_i64(101, 100_000) as i32,
            3 => rng.gen_range_i64(100_001, 1_000_000) as i32,
            _ => rng.gen_range_i64(1_000_001, 1_000_000_000) as i32,
        };

        let max_nh = std::cmp::min((h - 1) as usize, 100_000);
        let max_nv = std::cmp::min((w - 1) as usize, 100_000);

        let num_h: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, std::cmp::min(5, max_nh)),
            2 => rng.gen_range_usize(1, std::cmp::min(100, max_nh)),
            3 => rng.gen_range_usize(1, std::cmp::min(1000, max_nh)),
            _ => rng.gen_range_usize(1, max_nh),
        };
        let num_v: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(1, std::cmp::min(5, max_nv)),
            2 => rng.gen_range_usize(1, std::cmp::min(100, max_nv)),
            3 => rng.gen_range_usize(1, std::cmp::min(1000, max_nv)),
            _ => rng.gen_range_usize(1, max_nv),
        };

        let max_h_start = (h as i64 - num_h as i64) as i32;
        let h_start = if max_h_start <= 1 { 1 } else {
            rng.gen_range_i64(1, max_h_start as i64) as i32
        };
        let max_v_start = (w as i64 - num_v as i64) as i32;
        let v_start = if max_v_start <= 1 { 1 } else {
            rng.gen_range_i64(1, max_v_start as i64) as i32
        };

        let mk = rng.gen_range_usize(0, 7) as u8;

        let (rh, rw, mut hc, mut vc) = generate_test_case(h, w, num_h, num_v, h_start, v_start, mk);

        // Shuffle cuts for diversity (unverified, preserves distinctness and range)
        shuffle(&mut hc, &mut rng);
        shuffle(&mut vc, &mut rng);

        emit(rh, rw, hc, vc, &mut seen, &mut out, &mut count);
    }
}

fn shuffle(v: &mut Vec<i32>, rng: &mut Rng) {
    let n = v.len();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
}
