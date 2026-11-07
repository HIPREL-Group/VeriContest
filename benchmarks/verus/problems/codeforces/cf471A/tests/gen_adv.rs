use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s0: i32,
    s1: i32,
    s2: i32,
    s3: i32,
    s4: i32,
    s5: i32,
) -> (sticks: Vec<i32>)
    requires
        1 <= s0 <= 9,
        1 <= s1 <= 9,
        1 <= s2 <= 9,
        1 <= s3 <= 9,
        1 <= s4 <= 9,
        1 <= s5 <= 9,
    ensures
        sticks.len() == 6,
        forall|i: int| 0 <= i < 6 ==> 1 <= #[trigger] sticks@[i] as int <= 9,
{
    let mut sticks: Vec<i32> = Vec::new();
    sticks.push(s0);
    sticks.push(s1);
    sticks.push(s2);
    sticks.push(s3);
    sticks.push(s4);
    sticks.push(s5);
    assert(sticks@[0] == s0);
    assert(sticks@[1] == s1);
    assert(sticks@[2] == s2);
    assert(sticks@[3] == s3);
    assert(sticks@[4] == s4);
    assert(sticks@[5] == s5);
    sticks
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

fn build_input(sticks: &[i32]) -> String {
    let parts: Vec<String> = sticks.iter().map(|x| x.to_string()).collect();
    format!("{}\n", parts.join(" "))
}

fn build_output(r: i32) -> String {
    if r == 1 { "Bear\n".to_string() }
    else if r == 2 { "Elephant\n".to_string() }
    else { "Alien\n".to_string() }
}

fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(47101);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |sticks: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", sticks);
        if !seen.insert(key) { return; }
        let result = Solution::animal_type(sticks.clone());
        let inp = build_input(&sticks);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: Cover all "4 of L, 2 different" combos for Bear
    for leg in 1..=9 {
        for h in 1..=9 {
            for body in 1..=9 {
                if h == leg || body == leg { continue; }
                if h == body { continue; }
                let mut sticks = vec![leg, leg, leg, leg, h, body];
                shuffle(&mut rng, &mut sticks);
                emit(sticks, &mut seen, &mut out, &mut count);
                if count >= 80 { break; }
            }
            if count >= 80 { break; }
        }
        if count >= 80 { break; }
    }

    // Elephant cases: 4 of leg + 2 same different from leg
    for leg in 1..=9 {
        for hb in 1..=9 {
            if hb == leg { continue; }
            let mut sticks = vec![leg, leg, leg, leg, hb, hb];
            shuffle(&mut rng, &mut sticks);
            emit(sticks, &mut seen, &mut out, &mut count);
        }
    }

    // 6 of leg -> Elephant
    for leg in 1..=9 {
        emit(vec![leg, leg, leg, leg, leg, leg], &mut seen, &mut out, &mut count);
    }

    // 5 of leg + 1 -> Bear
    for leg in 1..=9 {
        for x in 1..=9 {
            if x == leg { continue; }
            let mut sticks = vec![leg, leg, leg, leg, leg, x];
            shuffle(&mut rng, &mut sticks);
            emit(sticks, &mut seen, &mut out, &mut count);
        }
    }

    // Alien: at most 3 of any
    while count < target_count {
        let mut sticks = Vec::with_capacity(6);
        for _ in 0..6 {
            sticks.push(rng.gen_range_i64(1, 9) as i32);
        }
        emit(sticks, &mut seen, &mut out, &mut count);
    }
}

