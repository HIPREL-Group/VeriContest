use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    homes: &Vec<i32>,
    aways: &Vec<i32>,
) -> (res: (Vec<i32>, Vec<i32>, usize))
    requires
        2 <= n <= 30,
        homes.len() == n,
        aways.len() == n,
        forall|i: int| 0 <= i < homes.len() as int ==> 1 <= #[trigger] homes[i] <= 100,
        forall|i: int| 0 <= i < aways.len() as int ==> 1 <= #[trigger] aways[i] <= 100,
        forall|i: int| 0 <= i < homes.len() as int ==> homes[i] as int != aways[i] as int,
    ensures
        2 <= res.2 <= 30,
        res.0.len() == res.2,
        res.1.len() == res.2,
        forall|i: int| 0 <= i < res.0.len() as int ==> 1 <= #[trigger] res.0[i] <= 100,
        forall|i: int| 0 <= i < res.1.len() as int ==> 1 <= #[trigger] res.1[i] <= 100,
        forall|i: int| 0 <= i < res.0.len() as int ==> res.0[i] as int != res.1[i] as int,
{
    let mut h: Vec<i32> = Vec::new();
    let mut a: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            h.len() == idx,
            a.len() == idx,
            homes.len() == n,
            aways.len() == n,
            forall|i: int| 0 <= i < idx as int ==> #[trigger] h[i] == homes[i],
            forall|i: int| 0 <= i < idx as int ==> #[trigger] a[i] == aways[i],
            forall|i: int| 0 <= i < homes.len() as int ==> 1 <= #[trigger] homes[i] <= 100,
            forall|i: int| 0 <= i < aways.len() as int ==> 1 <= #[trigger] aways[i] <= 100,
            forall|i: int| 0 <= i < homes.len() as int ==> homes[i] as int != aways[i] as int,
        decreases n - idx,
    {
        h.push(homes[idx]);
        a.push(aways[idx]);
        idx = idx + 1;
    }
    (h, a, n)
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

fn build_input(home: &[i32], away: &[i32]) -> String {
    let n = home.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", home[i], away[i]));
    }
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn random_team_pair(rng: &mut Rng, max: i64) -> (i32, i32) {
    loop {
        let h = rng.gen_range_i64(1, max) as i32;
        let a = rng.gen_range_i64(1, max) as i32;
        if h != a { return (h, a); }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x268AA);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 4 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 15),
            2 => rng.gen_range_usize(15, 25),
            _ => rng.gen_range_usize(25, 30),
        };
        let max = match tries % 3 {
            0 => 10i64,
            1 => 50i64,
            _ => 100i64,
        };
        let mut home = Vec::with_capacity(n);
        let mut away = Vec::with_capacity(n);
        for _ in 0..n {
            let (h, a) = random_team_pair(&mut rng, max);
            home.push(h);
            away.push(a);
        }
        let inp = build_input(&home, &away);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_host_guest_uniforms(home, away, n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

