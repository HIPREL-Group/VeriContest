use vstd::prelude::*;

verus! {

pub open spec fn is_spy(a: Seq<i64>, i: int) -> bool {
    &&& 0 <= i < a.len()
    &&& forall|j: int| 0 <= j < a.len() && j != i ==> a[j] != a[i]
    &&& forall|j: int, k: int| 0 <= j < a.len() && 0 <= k < a.len() && j != i && k != i ==> a[j] == a[k]
}

pub fn generate_test_case(
    n: usize,
    spy_idx: usize,
    common_val: i64,
    spy_val: i64,
) -> (res: Vec<i64>)
    requires
        3 <= n <= 100,
        spy_idx < n,
        common_val != spy_val,
    ensures
        3 <= res.len() <= 100,
        res.len() == n,
        exists|i: int| is_spy(res@, i),
        is_spy(res@, spy_idx as int),
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            3 <= n <= 100,
            spy_idx < n,
            common_val != spy_val,
            v.len() == i,
            forall|k: int| 0 <= k < i as int && k == spy_idx as int ==> #[trigger] v[k] == spy_val,
            forall|k: int| 0 <= k < i as int && k != spy_idx as int ==> #[trigger] v[k] == common_val,
        decreases n - i,
    {
        if i == spy_idx {
            v.push(spy_val);
        } else {
            v.push(common_val);
        }
        i = i + 1;
    }

    proof {
        assert(v.len() == n);
        assert(v[spy_idx as int] == spy_val);
        assert forall|j: int| 0 <= j < v.len() && j != spy_idx as int implies v[j] != v[spy_idx as int] by {
            assert(v[j] == common_val);
            assert(v[spy_idx as int] == spy_val);
        }
        assert forall|j: int, k: int| 0 <= j < v.len() && 0 <= k < v.len() && j != spy_idx as int && k != spy_idx as int implies v[j] == v[k] by {
            assert(v[j] == common_val);
            assert(v[k] == common_val);
        }
        assert(is_spy(v@, spy_idx as int));
    }

    v
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn make_spy(n: usize, base: i64, spy: i64, idx: usize) -> Vec<i64> {
    let mut a = vec![base; n];
    a[idx] = spy;
    a
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Bundle all-corner cases
    {
        let mut cases: Vec<Vec<i64>> = Vec::new();
        // boundary-spies
        cases.push(make_spy(3, 5, 1, 0));
        cases.push(make_spy(3, 5, 1, 1));
        cases.push(make_spy(3, 5, 1, 2));
        cases.push(make_spy(100, 5, 1, 0));
        cases.push(make_spy(100, 5, 1, 50));
        cases.push(make_spy(100, 5, 1, 99));
        let answers: Vec<usize> = cases.iter().map(|a| Solution::spy_index(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => 100,
        };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 3,
                1 => 4,
                2 => rng.gen_range_usize(5, 20),
                3 => rng.gen_range_usize(20, 50),
                _ => rng.gen_range_usize(50, 100),
            };
            let base = rng.gen_range_i64(1, 100);
            let mut spy = rng.gen_range_i64(1, 100);
            if spy == base { spy = if base == 100 { 1 } else { base + 1 }; }
            let idx = rng.gen_range_usize(0, n - 1);
            cases.push(make_spy(n, base, spy, idx));
        }
        let answers: Vec<usize> = cases.iter().map(|a| Solution::spy_index(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

