use vstd::prelude::*;

verus! {

pub fn generate_test_case(now_raw: i32, alarm_raw: i32) -> (res: (i32, i32))
    requires
        0 <= now_raw,
        0 <= alarm_raw,
    ensures
        0 <= res.0 < 1440,
        0 <= res.1 < 1440,
{
    let now = now_raw % 1440;
    let alarm = alarm_raw % 1440;
    assert(0 <= now < 1440);
    assert(0 <= alarm < 1440);
    (now, alarm)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    let h = rng.gen_range_i32(0, 23);
    let m = rng.gen_range_i32(0, 59);
    match mode {
        0 => (h, m, vec![(rng.gen_range_i32(0, 23), rng.gen_range_i32(0, 59))]),
        1 => {
            let n = rng.gen_range_usize(2, 10);
            let alarms: Vec<(i32, i32)> = (0..n).map(|_| (rng.gen_range_i32(0, 23), rng.gen_range_i32(0, 59))).collect();
            (h, m, alarms)
        }
        2 => {
            // Same time as one alarm => 0 wait
            (h, m, vec![(h, m)])
        }
        3 => {
            // alarm at 23:59
            (h, m, vec![(23, 59)])
        }
        4 => {
            // alarm at 00:00
            (h, m, vec![(0, 0)])
        }
        5 => {
            // many alarms
            let n = rng.gen_range_usize(20, 50);
            let alarms: Vec<(i32, i32)> = (0..n).map(|_| (rng.gen_range_i32(0, 23), rng.gen_range_i32(0, 59))).collect();
            (h, m, alarms)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let alarms: Vec<(i32, i32)> = (0..n).map(|_| (rng.gen_range_i32(0, 23), rng.gen_range_i32(0, 59))).collect();
            (h, m, alarms)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1714);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 7;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

