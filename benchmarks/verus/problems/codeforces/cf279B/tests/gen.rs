use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    books: Vec<i32>,
    t: i64,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i64))
    requires
        1 <= books.len() <= 99_999,
        2 <= t <= 999_999_999,
        forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0@.len() ==> 1 <= #[trigger] result.0@[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (books, t)
    } else if mutation_kind == 1 && t < 1_000_000_000 {
        // nudge t up
        (books, t + 1)
    } else if mutation_kind == 2 && t > 1 {
        // nudge t down
        (books, t - 1)
    } else if mutation_kind == 3 {
        // t = 1 (min boundary)
        (books, 1)
    } else if mutation_kind == 4 {
        // t = max boundary
        (books, 1_000_000_000)
    } else if mutation_kind == 5 {
        // set all books to 1
        let mut d = books;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == books.len(),
                1 <= d.len() <= 99_999,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == books[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 10_000,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, t)
    } else if mutation_kind == 6 {
        // set all books to 10_000
        let mut d = books;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == books.len(),
                1 <= d.len() <= 99_999,
                forall|j: int| 0 <= j < i ==> d[j] == 10_000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == books[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 10_000,
            decreases d.len() - i,
        {
            d.set(i, 10_000);
            i += 1;
        }
        (d, t)
    } else if mutation_kind == 7 && books.len() < 100_000 {
        // grow array by pushing element
        let mut d = books;
        d.push(1);
        (d, t)
    } else if mutation_kind == 8 && books.len() > 1 {
        // shrink array by popping element
        let mut d = books;
        d.pop();
        (d, t)
    } else if mutation_kind == 9 {
        // nudge first book value up (if < 10_000)
        let mut d = books;
        if d[0] < 10_000 {
            d.set(0, d[0] + 1);
        }
        (d, t)
    } else if mutation_kind == 10 {
        // nudge first book value down (if > 1)
        let mut d = books;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, t)
    } else if mutation_kind == 11 {
        // set first book to 1 (min boundary)
        let mut d = books;
        d.set(0, 1);
        (d, t)
    } else if mutation_kind == 12 {
        // set first book to 10_000 (max boundary)
        let mut d = books;
        d.set(0, 10_000);
        (d, t)
    } else if mutation_kind == 13 {
        // double t if within range
        if t <= 500_000_000 {
            (books, t * 2)
        } else {
            (books, t)
        }
    } else if mutation_kind == 14 {
        // halve t
        let half = t / 2;
        if half >= 1 {
            (books, half)
        } else {
            (books, 1)
        }
    } else {
        // fallback: identity
        (books, t)
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

fn build_input(books: &[i32], t: i64) -> String {
    let mut s = format!("{} {}\n", books.len(), t);
    let parts: Vec<String> = books.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(279);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    {
        let books = vec![3, 1, 2, 1];
        let t = 5;
        let inp = build_input(&books, t);
        if seen.insert(inp.clone()) {
            let ans = Solution::max_books_read(books, t);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
    {
        let books = vec![2, 2, 3];
        let t = 3;
        let inp = build_input(&books, t);
        if seen.insert(inp.clone()) {
            let ans = Solution::max_books_read(books, t);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 5000),
        };
        let t = rng.gen_range_i64(1, 1_000_000_000);
        let books: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10000) as i32).collect();
        let inp = build_input(&books, t);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::max_books_read(books, t);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

