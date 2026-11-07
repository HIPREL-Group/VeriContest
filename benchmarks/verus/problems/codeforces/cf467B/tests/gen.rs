use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: Vec<i32>,
    n_param: i32,
    k_param: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<i32>))
    requires
        2 <= values.len() && values.len() <= 1001,
        0 <= (n_param as int) && 1 <= (k_param as int) && (k_param as int) <= (n_param as int) && (n_param as int) <= 20,
        forall|i: int| 0 <= i < values@.len() ==> (1 <= #[trigger] values@[i] && (values@[i] as int) < 1048576),
    ensures
        2 <= result.2.len() && result.2.len() <= 1001,
        0 <= (result.0 as int) && 1 <= (result.1 as int) && (result.1 as int) <= (result.0 as int) && (result.0 as int) <= 20,
        forall|i: int| 0 <= i < result.2@.len() ==> (1 <= #[trigger] result.2@[i] && (result.2@[i] as int) < 1048576),
{
    if mutation_kind == 0 {
        // identity
        (n_param, k_param, values)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        (n_param, k_param, v)
    } else if mutation_kind == 2 {
        // set first element to max boundary (1048575 = 2^20 - 1)
        let mut v = values;
        v.set(0, 1048575);
        (n_param, k_param, v)
    } else if mutation_kind == 3 {
        // set last element to 1 (min boundary for fedor)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        (n_param, k_param, v)
    } else if mutation_kind == 4 {
        // set last element to max boundary
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1048575);
        (n_param, k_param, v)
    } else if mutation_kind == 5 && values.len() < 1001 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        (n_param, k_param, v)
    } else if mutation_kind == 6 && values.len() > 2 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        (n_param, k_param, v)
    } else if mutation_kind == 7 {
        // set all elements equal to the first element
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                2 <= len <= 1001,
                1 <= val && (val as int) < 1048576,
                forall|j: int| 0 <= j && j < (i as int) ==> #[trigger] v@[j] == val,
                forall|j: int| (i as int) <= j && j < (len as int) ==> (1 <= #[trigger] v@[j] && (v@[j] as int) < 1048576),
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        (n_param, k_param, v)
    } else if mutation_kind == 8 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (n_param, k_param, v)
    } else if mutation_kind == 9 {
        // set k = n (maximize friends — all differing bits allowed)
        (n_param, n_param, values)
    } else if mutation_kind == 10 {
        // set k = 1 (minimize friends)
        (n_param, 1, values)
    } else {
        // fallback: identity
        (n_param, k_param, values)
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

fn random_army_array(rng: &mut Rng, len: usize, n: i32) -> Vec<i32> {
    let max_val = (1i64 << n) - 1;
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, max_val) as i32);
    }
    arr
}

fn build_input(n: i32, k: i32, armies: &[i32]) -> String {
    let m = armies.len() - 1;
    let mut s = format!("{} {} {}\n", n, m, k);
    for &a in armies {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(467);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, k: i32, armies: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if armies.len() < 2 { return; }
        let key = format!("{},{},{:?}", n, k, armies);
        if !seen.insert(key) { return; }
        let result = Solution::count_fedor_friends(n, k, armies.clone());
        let inp = build_input(n, k, &armies);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(7, 1, vec![8, 5, 111, 17], &mut seen, &mut out, &mut count);
    emit(3, 3, vec![1, 2, 3, 4], &mut seen, &mut out, &mut count);

    // Hand-crafted edges
    let edge_cases: Vec<(i32, i32, Vec<i32>)> = vec![
        (1, 1, vec![1, 1]),
        (1, 1, vec![1, 1, 1]),
        (20, 1, vec![1, 1048575]),
        (20, 20, vec![1, 1048575]),
        (20, 10, vec![1, 524287, 1048575]),
        (1, 1, vec![1, 1, 1, 1, 1]),
        (5, 2, vec![3, 7, 12, 31, 1]),
        (10, 3, vec![1023, 512, 256, 1, 1023]),
        (15, 5, vec![16384, 32767, 1, 12345, 32767]),
    ];

    for (n, k, armies) in &edge_cases {
        emit(*n, *k, armies.clone(), &mut seen, &mut out, &mut count);
    }

    let n_values: Vec<i32> = vec![1, 2, 3, 5, 10, 15, 20];

    // Random arrays
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(3, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1001),
        };
        let n = n_values[rng.gen_range_usize(0, n_values.len() - 1)];
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let arr = random_army_array(&mut rng, len, n);
        emit(n, k, arr, &mut seen, &mut out, &mut count);
    }
}

