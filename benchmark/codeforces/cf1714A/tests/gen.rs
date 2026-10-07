use vstd::prelude::*;

verus! {

pub fn generate_test_case(now: i32, alarms: Vec<i32>, mutation_kind: u8) -> (result: (i32, Vec<i32>))
    requires
        0 <= now < 1440,
        1 <= alarms.len() <= 10,
        forall|j: int| 0 <= j < alarms.len() as int ==> 0 <= #[trigger] alarms[j] < 1440,
    ensures
        0 <= result.0 < 1440,
        1 <= result.1.len() <= 10,
        forall|j: int| 0 <= j < result.1.len() as int ==> 0 <= #[trigger] result.1[j] < 1440,
{
    if mutation_kind == 0 {
        // identity
        (now, alarms)
    } else if mutation_kind == 1 && now < 1439 {
        // nudge now up
        (now + 1, alarms)
    } else if mutation_kind == 2 && now > 0 {
        // nudge now down
        (now - 1, alarms)
    } else if mutation_kind == 3 {
        // now = 0 (midnight)
        (0, alarms)
    } else if mutation_kind == 4 {
        // now = 1439 (23:59)
        (1439, alarms)
    } else if mutation_kind == 5 {
        // set last alarm to 0
        let mut a = alarms;
        let last = a.len() - 1;
        a.set(last, 0);
        (now, a)
    } else if mutation_kind == 6 {
        // set last alarm to 1439
        let mut a = alarms;
        let last = a.len() - 1;
        a.set(last, 1439);
        (now, a)
    } else if mutation_kind == 7 {
        // set first alarm to match now (zero wait)
        let mut a = alarms;
        a.set(0, now);
        (now, a)
    } else if mutation_kind == 8 && alarms.len() < 10 {
        // grow alarms by one (push 0)
        let mut a = alarms;
        a.push(0);
        (now, a)
    } else if mutation_kind == 9 && alarms.len() > 1 {
        // shrink alarms by one (pop)
        let mut a = alarms;
        a.pop();
        (now, a)
    } else if mutation_kind == 10 {
        // set all alarms to 0
        let ghost old_alarms = alarms;
        let mut a = alarms;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == old_alarms.len(),
                1 <= a.len() <= 10,
                forall|j: int| 0 <= j < i ==> a[j] == 0i32,
                forall|j: int| i <= j < a.len() as int ==> a[j] == old_alarms[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        (now, a)
    } else if mutation_kind == 11 {
        // set all alarms to now (all same wait = 0)
        let ghost old_alarms = alarms;
        let mut a = alarms;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == old_alarms.len(),
                1 <= a.len() <= 10,
                0 <= now < 1440,
                forall|j: int| 0 <= j < i ==> a[j] == now,
                forall|j: int| i <= j < a.len() as int ==> a[j] == old_alarms[j],
            decreases a.len() - i,
        {
            a.set(i, now);
            i += 1;
        }
        (now, a)
    } else {
        // fallback: identity
        (now, alarms)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

// (h, m, alarms[(h_i, m_i)])
type TC = (i32, i32, Vec<(i32, i32)>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (h, m, alarms) in cases {
        s.push_str(&format!("{} {} {}\n", alarms.len(), h, m));
        for (ah, am) in alarms {
            s.push_str(&format!("{} {}\n", ah, am));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (h, m, alarms) in cases {
        let now = h * 60 + m;
        let alarm_minutes: Vec<i32> = alarms.iter().map(|(h, m)| h * 60 + m).collect();
        let ans = Solution::min_wait_minutes(now, alarm_minutes);
        s.push_str(&format!("{} {}\n", ans / 60, ans % 60));
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> TC {
    let n = rng.gen_range_usize(1, max_n);
    let h = rng.gen_range_i32(0, 23);
    let m = rng.gen_range_i32(0, 59);
    let alarms: Vec<(i32, i32)> = (0..n).map(|_| (rng.gen_range_i32(0, 23), rng.gen_range_i32(0, 59))).collect();
    (h, m, alarms)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1714);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (8, 0, vec![(7, 30), (10, 30)]),
        (0, 0, vec![(0, 0)]),
        (23, 59, vec![(0, 0)]),
        (12, 30, vec![(13, 0), (14, 0), (15, 0)]),
        (5, 30, vec![(5, 30)]),
        (10, 0, vec![(11, 0), (12, 0), (13, 0), (14, 0), (15, 0)]),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng, 20));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

