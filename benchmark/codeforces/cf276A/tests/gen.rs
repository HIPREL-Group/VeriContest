use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    restaurants: Vec<(i64, i64)>,
    k: i64,
    mutation_kind: u8,
) -> (result: (Vec<(i64, i64)>, i64))
    requires
        restaurants.len() >= 1,
        restaurants.len() <= 10000,
        1 <= k <= 1000000000,
        forall|i: int| 0 <= i < restaurants.len() ==>
            1 <= #[trigger] restaurants@[i].0 <= 1000000000,
        forall|i: int| 0 <= i < restaurants.len() ==>
            1 <= #[trigger] restaurants@[i].1 <= 1000000000,
    ensures
        result.0.len() >= 1,
        result.0.len() <= 10000,
        1 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==>
            1 <= #[trigger] result.0@[i].0 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==>
            1 <= #[trigger] result.0@[i].1 <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        (restaurants, k)
    } else if mutation_kind == 1 {
        // set last restaurant's f to 1
        let mut r = restaurants;
        let last = r.len() - 1;
        let old = r[last];
        r.set(last, (1i64, old.1));
        (r, k)
    } else if mutation_kind == 2 {
        // set last restaurant's f to max
        let mut r = restaurants;
        let last = r.len() - 1;
        let old = r[last];
        r.set(last, (1000000000i64, old.1));
        (r, k)
    } else if mutation_kind == 3 {
        // set last restaurant's t to 1
        let mut r = restaurants;
        let last = r.len() - 1;
        let old = r[last];
        r.set(last, (old.0, 1i64));
        (r, k)
    } else if mutation_kind == 4 {
        // set last restaurant's t to max
        let mut r = restaurants;
        let last = r.len() - 1;
        let old = r[last];
        r.set(last, (old.0, 1000000000i64));
        (r, k)
    } else if mutation_kind == 5 && restaurants.len() < 10000 {
        // grow: push one element
        let mut r = restaurants;
        r.push((1i64, 1i64));
        (r, k)
    } else if mutation_kind == 6 && restaurants.len() > 1 {
        // shrink: pop one element
        let mut r = restaurants;
        r.pop();
        (r, k)
    } else if mutation_kind == 7 && k < 1000000000 {
        // nudge k up
        (restaurants, k + 1)
    } else if mutation_kind == 8 && k > 1 {
        // nudge k down
        (restaurants, k - 1)
    } else if mutation_kind == 9 {
        // set k to 1
        (restaurants, 1i64)
    } else if mutation_kind == 10 {
        // set k to max
        (restaurants, 1000000000i64)
    } else if mutation_kind == 11 {
        // set all restaurants to (1, 1)
        let n = restaurants.len();
        let mut r = restaurants;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 10000,
                forall|j: int| 0 <= j < i ==> r[j] == (1i64, 1i64),
                forall|j: int| 0 <= j < r.len() ==>
                    1 <= #[trigger] r@[j].0 <= 1000000000,
                forall|j: int| 0 <= j < r.len() ==>
                    1 <= #[trigger] r@[j].1 <= 1000000000,
            decreases r.len() - i,
        {
            r.set(i, (1i64, 1i64));
            i += 1;
        }
        (r, k)
    } else if mutation_kind == 12 {
        // set all restaurants to (1000000000, 1000000000)
        let n = restaurants.len();
        let mut r = restaurants;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 10000,
                forall|j: int| 0 <= j < i ==> r[j] == (1000000000i64, 1000000000i64),
                forall|j: int| 0 <= j < r.len() ==>
                    1 <= #[trigger] r@[j].0 <= 1000000000,
                forall|j: int| 0 <= j < r.len() ==>
                    1 <= #[trigger] r@[j].1 <= 1000000000,
            decreases r.len() - i,
        {
            r.set(i, (1000000000i64, 1000000000i64));
            i += 1;
        }
        (r, k)
    } else {
        // fallback
        (restaurants, k)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
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

fn build_input(restaurants: &[(i64, i64)], k: i64) -> String {
    let mut s = format!("{} {}\n", restaurants.len(), k);
    for &(f, t) in restaurants {
        s.push_str(&format!("{} {}\n", f, t));
    }
    s
}

fn build_output(ans: i64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(276);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples
    {
        let r = vec![(3i64, 3i64), (4, 5)];
        let k = 5;
        let inp = build_input(&r, k);
        if seen.insert(inp.clone()) {
            let ans = Solution::max_lunch_joy(r, k);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
    {
        let r = vec![(5i64, 8i64), (3, 6), (2, 3), (2, 2)];
        let k = 6;
        let inp = build_input(&r, k);
        if seen.insert(inp.clone()) {
            let ans = Solution::max_lunch_joy(r, k);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let max_v = match tries % 3 {
            0 => 100i64,
            1 => 1_000_000i64,
            _ => 1_000_000_000i64,
        };
        let k = rng.gen_range_i64(1, max_v);
        let restaurants: Vec<(i64, i64)> = (0..n).map(|_| (rng.gen_range_i64(1, max_v), rng.gen_range_i64(1, max_v))).collect();
        let inp = build_input(&restaurants, k);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::max_lunch_joy(restaurants, k);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

