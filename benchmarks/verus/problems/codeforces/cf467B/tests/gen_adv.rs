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
        (n_param, k_param, values)
    } else if mutation_kind == 1 {
        let mut v = values;
        v.set(0, 1);
        (n_param, k_param, v)
    } else if mutation_kind == 2 {
        let mut v = values;
        v.set(0, 1048575);
        (n_param, k_param, v)
    } else if mutation_kind == 3 {
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        (n_param, k_param, v)
    } else if mutation_kind == 4 {
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1048575);
        (n_param, k_param, v)
    } else if mutation_kind == 5 && values.len() < 1001 {
        let mut v = values;
        v.push(1);
        (n_param, k_param, v)
    } else if mutation_kind == 6 && values.len() > 2 {
        let mut v = values;
        v.pop();
        (n_param, k_param, v)
    } else if mutation_kind == 7 {
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
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (n_param, k_param, v)
    } else if mutation_kind == 9 {
        (n_param, n_param, values)
    } else if mutation_kind == 10 {
        (n_param, 1, values)
    } else {
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
    let target_count: usize = 200;
    let mut rng = Rng::new(46701);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Adversarial / extreme stress cases: max n, max armies, max m
    // m_max = 1000 means armies has 1001 entries
    let max_armies_all_max: Vec<i32> = vec![1048575; 1001];
    emit(20, 20, max_armies_all_max.clone(), &mut seen, &mut out, &mut count);
    emit(20, 1, max_armies_all_max.clone(), &mut seen, &mut out, &mut count);

    let max_armies_all_min: Vec<i32> = vec![1; 1001];
    emit(20, 20, max_armies_all_min.clone(), &mut seen, &mut out, &mut count);
    emit(20, 1, max_armies_all_min.clone(), &mut seen, &mut out, &mut count);
    emit(1, 1, max_armies_all_min.clone(), &mut seen, &mut out, &mut count);

    // Mix of min and max
    let mixed_armies: Vec<i32> = (0..1001).map(|i| if i % 2 == 0 { 1 } else { 1048575 }).collect();
    emit(20, 1, mixed_armies.clone(), &mut seen, &mut out, &mut count);
    emit(20, 20, mixed_armies.clone(), &mut seen, &mut out, &mut count);
    emit(20, 10, mixed_armies.clone(), &mut seen, &mut out, &mut count);

    // Adversarial: armies all differ from fedor in exactly 1, k or k+1 bits
    for k in [1i32, 5, 10, 15, 20] {
        let n = 20;
        let fedor: i32 = 0xAAAAA & ((1 << n) - 1);
        let mut armies: Vec<i32> = Vec::new();
        for j in 0..1000 {
            // flip first (j%n) bits (consistent pattern)
            let flips = (j % (n as i32)) as i32 + 1;
            let mut b = fedor;
            let mut bit = 0;
            let mut count_flipped = 0;
            while count_flipped < flips && bit < n {
                b ^= 1 << bit;
                bit += 1;
                count_flipped += 1;
            }
            armies.push(if b == 0 { 1 } else { b });
        }
        armies.push(if fedor == 0 { 1 } else { fedor });
        emit(n, k, armies, &mut seen, &mut out, &mut count);
    }

    let n_values: Vec<i32> = vec![1, 2, 3, 5, 10, 15, 20];
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 5),
        (3, 20),
        (21, 100),
        (101, 500),
        (501, 1001),
    ];

    // Stress: use mostly large arrays
    while count < target_count {
        let len = match count % 7 {
            0 | 1 | 2 => rng.gen_range_usize(800, 1001),  // large
            3 | 4 => rng.gen_range_usize(101, 500),
            5 => rng.gen_range_usize(21, 100),
            _ => {
                let (lo, hi) = size_classes[rng.gen_range_usize(0, size_classes.len() - 1)];
                rng.gen_range_usize(lo, hi)
            }
        };
        let n = n_values[rng.gen_range_usize(0, n_values.len() - 1)];
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let arr = random_army_array(&mut rng, len, n);
        emit(n, k, arr, &mut seen, &mut out, &mut count);
    }
}

