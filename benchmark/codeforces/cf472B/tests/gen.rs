use vstd::prelude::*;

verus! {

pub fn generate_test_case(k: usize, n: usize, floor_vals: Vec<i32>, mutation_kind: u8) -> (result: (usize, Vec<i32>))
    requires
        1 <= k <= 2000,
        1 <= n <= 2000,
        floor_vals.len() == n,
        forall|i: int| 0 <= i < n as int ==> 2 <= (#[trigger] floor_vals[i] as int) && (floor_vals[i] as int) <= 2000,
    ensures
        1 <= (result.0 as int) && (result.0 as int) <= 2000,
        1 <= result.1.len() && result.1.len() <= 2000,
        forall|i: int|
            0 <= i < result.1.len() ==> 2 <= #[trigger] (result.1[i] as int) && (result.1[i] as int) <= 2000,
{
    if mutation_kind == 0 {
        // identity
        (k, floor_vals)
    } else if mutation_kind == 1 {
        // set all elements to 2 (minimum floor)
        let mut y = floor_vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 2000,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] y[j] == 2i32),
                forall|j: int| i as int <= j < n as int ==> 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000,
            decreases n - i,
        {
            y.set(i, 2i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000 by {}
        (k, y)
    } else if mutation_kind == 2 {
        // set all elements to 2000 (maximum floor)
        let mut y = floor_vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 2000,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] y[j] == 2000i32),
                forall|j: int| i as int <= j < n as int ==> 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000,
            decreases n - i,
        {
            y.set(i, 2000i32);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000 by {}
        (k, y)
    } else if mutation_kind == 3 && floor_vals.len() >= 1 {
        // flip first element to (2002 - val), keeping in [2, 2000]
        let mut y = floor_vals;
        let old = y[0];
        let new_val = 2002i32 - old;
        assert(2 <= new_val <= 2000);
        y.set(0, new_val);
        assert forall|j: int| 0 <= j < y.len() implies 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000 by {}
        (k, y)
    } else if mutation_kind == 4 && floor_vals.len() >= 1 {
        // flip last element to (2002 - val)
        let mut y = floor_vals;
        let last = y.len() - 1;
        let old = y[last];
        let new_val = 2002i32 - old;
        assert(2 <= new_val <= 2000);
        y.set(last, new_val);
        assert forall|j: int| 0 <= j < y.len() implies 2 <= (#[trigger] y[j] as int) && (y[j] as int) <= 2000 by {}
        (k, y)
    } else if mutation_kind == 5 {
        // set k to 1 (minimum capacity)
        (1usize, floor_vals)
    } else if mutation_kind == 6 {
        // set k to 2000 (maximum capacity)
        (2000usize, floor_vals)
    } else {
        // fallback: identity
        (k, floor_vals)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

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

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(n: usize, k: usize, floors: &[i32]) -> String {
    let mut s = format!("{} {}\n", n, k);
    let parts: Vec<String> = floors.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(472);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |k: usize, floors: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if floors.is_empty() || k == 0 { return; }
        let n = floors.len();
        let key = format!("{}_{}_{:?}", n, k, floors);
        if !seen.insert(key) { return; }
        let result = Solution::min_elevator_return_time(k, floors.clone());
        let inp = build_input(n, k, &floors);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(2, vec![2, 3, 4], &mut seen, &mut out, &mut count);
    emit(2, vec![50, 100, 50, 100], &mut seen, &mut out, &mut count);
    emit(3, vec![2; 10], &mut seen, &mut out, &mut count);

    emit(1, vec![2], &mut seen, &mut out, &mut count);
    emit(1, vec![2000], &mut seen, &mut out, &mut count);
    emit(2000, vec![2; 50], &mut seen, &mut out, &mut count);
    emit(1, vec![2, 2, 2, 2, 2], &mut seen, &mut out, &mut count);
    emit(5, vec![2000, 2000, 2000, 2000, 2000], &mut seen, &mut out, &mut count);
    emit(1, vec![2, 3, 4, 5, 6, 7, 8, 9, 10], &mut seen, &mut out, &mut count);
    emit(2, vec![1000, 1000], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 300),
            _ => rng.gen_range_usize(50, 500),
        };
        let k = rng.gen_range_usize(1, 50);
        let floors: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(2, 2000) as i32).collect();
        emit(k, floors, &mut seen, &mut out, &mut count);
    }
}

