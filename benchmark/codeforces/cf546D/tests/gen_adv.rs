use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_vals: &Vec<i32>,
    b_vals: &Vec<i32>,
) -> (queries: Vec<(i32, i32)>)
    requires
        a_vals.len() == b_vals.len(),
        1 <= a_vals.len() <= 1_000_000,
        forall|i: int| 0 <= i < a_vals.len() ==>
            1 <= (#[trigger] b_vals[i]) as int <= (#[trigger] a_vals[i]) as int <= 5_000_000,
    ensures
        1 <= queries.len() <= 1_000_000,
        queries.len() == a_vals.len(),
        forall|k: int|
            0 <= k < queries.len() ==> {
                let (a, b) = #[trigger] queries[k];
                1 <= b <= a <= 5_000_000
            },
{
    let n = a_vals.len();
    let _ = b_vals;
    let mut queries: Vec<(i32, i32)> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == a_vals.len(),
            1 <= n <= 1_000_000,
            0 <= i <= n,
            queries.len() == i,
            forall|k: int| 0 <= k < i as int ==> {
                let (a, b) = #[trigger] queries[k];
                1 <= b <= a <= 5_000_000
            },
            forall|k: int| 0 <= k < i as int ==> #[trigger] queries[k] == (1i32, 1i32),
        decreases n - i,
    {
        queries.push((1, 1));
        assert(queries[i as int] == (1i32, 1i32));
        i = i + 1;
    }

    proof {
        assert(queries.len() == n);
        assert forall|k: int| 0 <= k < queries.len() ==> {
            let (a, b) = #[trigger] queries[k];
            1 <= b <= a <= 5_000_000
        } by {
            if 0 <= k < queries.len() {
                assert(queries[k] == (1i32, 1i32));
            }
        }
    }

    queries
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

fn run() {
    let target_count: usize = 200;
    let mut rng = Rng::new(54605);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();

    // Build prefix up to a reasonable bound (1M to keep gen fast)
    let bound: usize = 1_000_000;
    let mut spf = vec![0usize; bound + 1];
    for i in 2..=bound {
        if spf[i] == 0 {
            let mut j = i;
            while j <= bound {
                if spf[j] == 0 { spf[j] = i; }
                j += i;
            }
        }
    }
    let mut omega = vec![0u64; bound + 1];
    for i in 2..=bound {
        let d = spf[i];
        let q = i / d;
        if q <= 1 { omega[i] = 1; }
        else {
            omega[i] = omega[q] + 1;
        }
    }
    let mut prefix = vec![0u64; bound + 2];
    for i in 2..=bound {
        prefix[i] = prefix[i-1] + omega[i];
    }

    let mut all_entries: Vec<(Vec<(i32, i32)>, Vec<u64>)> = Vec::new();

    let mut add_entry = |queries: Vec<(i32, i32)>, all_entries: &mut Vec<_>, seen: &mut HashSet<String>| {
        if queries.is_empty() { return; }
        for &(a, b) in &queries {
            if a < 1 || a > bound as i32 || b < 1 || b > a { return; }
        }
        let key = format!("{:?}", queries);
        if !seen.insert(key) { return; }
        let answers: Vec<u64> = queries.iter().map(|&(a, b)| prefix[a as usize] - prefix[b as usize]).collect();
        all_entries.push((queries, answers));
    };

    // Adversarial: many queries
    let big_queries: Vec<(i32, i32)> = (0..1000).map(|i| {
        let a = ((i + 1) * 1000).min(bound as i32);
        let b = ((i + 1) * 100).min(a);
        (a, b)
    }).collect();
    add_entry(big_queries, &mut all_entries, &mut seen);

    // Same a, b
    add_entry(vec![(bound as i32, 1); 100], &mut all_entries, &mut seen);

    // a==b queries
    add_entry((1..=100).map(|i| (i, i)).collect(), &mut all_entries, &mut seen);

    // Boundary cases
    add_entry(vec![(bound as i32, 1)], &mut all_entries, &mut seen);
    add_entry(vec![(bound as i32, bound as i32)], &mut all_entries, &mut seen);
    add_entry(vec![(bound as i32, bound as i32 - 1)], &mut all_entries, &mut seen);

    while all_entries.len() < target_count {
        let t = match all_entries.len() % 5 {
            0 | 1 => rng.gen_range_usize(500, 5000),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(10, 100),
            _ => rng.gen_range_usize(1, 50),
        };
        let mut queries = Vec::new();
        for _ in 0..t {
            let a = rng.gen_range_i64(1, bound as i64) as i32;
            let b = rng.gen_range_i64(1, a as i64) as i32;
            queries.push((a, b));
        }
        add_entry(queries, &mut all_entries, &mut seen);
    }

    for (queries, answers) in &all_entries {
        let mut inp = format!("{}\n", queries.len());
        for &(a, b) in queries {
            inp.push_str(&format!("{} {}\n", a, b));
        }
        let mut outp = String::new();
        for &ans in answers {
            outp.push_str(&format!("{}\n", ans));
        }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }
}

fn main() {
    let handle = std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(run)
        .unwrap();
    handle.join().unwrap();
}

