use vstd::prelude::*;

verus! {

proof fn trip_prefix_equal(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>, d: Seq<i32>, end: int)
    requires 0 <= end <= a.len(), end <= b.len(), end <= c.len(), end <= d.len(),
        forall|i: int| 0 <= i < end ==> #[trigger] a[i] == c[i],
        forall|i: int| 0 <= i < end ==> #[trigger] b[i] == d[i],
    ensures prefix_sum_entries(a, end) == prefix_sum_entries(c, end),
        prefix_sum_exits(b, end) == prefix_sum_exits(d, end),
        prefix_passengers(a, b, end) == prefix_passengers(c, d, end),
    decreases end,
{
    if end > 0 { trip_prefix_equal(a, b, c, d, end - 1); }
}
pub fn generate_test_case(raw_exits: Vec<i32>, raw_entries: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 2 <= result.0.len() <= 1000, result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        result.0[0] == 0, result.1[result.0.len() - 1] == 0,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= prefix_passengers(result.1@, result.0@, i),
        prefix_passengers(result.1@, result.0@, result.0.len() as int) == 0,
{
    let n = if raw_exits.len() < 2 { 2usize } else if raw_exits.len() > 1000 { 1000usize } else { raw_exits.len() };
    let mut exits: Vec<i32> = Vec::new();
    let mut entries: Vec<i32> = Vec::new();
    let mut passengers = 0i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 1000, exits.len() == i, entries.len() == i,
            0 <= passengers <= 1000 * (n - i),
            passengers == prefix_passengers(entries@, exits@, i as int),
            i > 0 ==> exits[0] == 0,
            i == n ==> entries[i - 1] == 0,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] exits[j] <= 1000,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] entries[j] <= 1000,
            forall|j: int| 0 <= j < i ==> #[trigger] exits[j] <= prefix_passengers(entries@, exits@, j),
        decreases n - i,
    {
        let capacity = 1000 * ((n - i - 1) as i32);
        let min_exit = if passengers > capacity { passengers - capacity } else { 0 };
        let max_exit = if passengers > 1000 { 1000 } else { passengers };
        let x = if i < raw_exits.len() { raw_exits[i] } else { 0 };
        let x = if x < min_exit { min_exit } else if x > max_exit { max_exit } else { x };
        let max_entry = capacity - passengers + x;
        let max_entry = if max_entry > 1000 { 1000 } else { max_entry };
        let y = if i < raw_entries.len() { raw_entries[i] } else { 0 };
        let y = if y < 0 { 0 } else if y > max_entry { max_entry } else { y };
        let ghost old_exits = exits@;
        let ghost old_entries = entries@;
        exits.push(x); entries.push(y);
        proof {
            trip_prefix_equal(entries@, exits@, old_entries, old_exits, i as int);
            assert forall|j: int| 0 <= j <= i implies
                #[trigger] exits[j] <= prefix_passengers(entries@, exits@, j) by {
                trip_prefix_equal(entries@, exits@, old_entries, old_exits, j);
                if j < i { assert(old_exits[j] <= prefix_passengers(old_entries, old_exits, j)); }
            }
        }
        passengers = passengers - x + y;
        i += 1;
    }
    (exits, entries)
}


pub open spec fn prefix_sum_entries(entries: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_entries(entries, end - 1) + entries[end - 1] as int
    }
}

pub open spec fn prefix_sum_exits(exits: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        prefix_sum_exits(exits, end - 1) + exits[end - 1] as int
    }
}

pub open spec fn prefix_passengers(entries: Seq<i32>, exits: Seq<i32>, end: int) -> int {
    prefix_sum_entries(entries, end) - prefix_sum_exits(exits, end)
}

// Generate a valid test case from a sequence of "net changes" that are non-negative
// at the current count. We build entries[i], exits[i] such that exits[0]=0, entries[last]=0,
// sum of (entries - exits) over all = 0, and at every point exits[i] <= current passengers.
//
// Strategy: take current_count c_i (c_0 = 0). Choose b_i (entries) and a_i (exits) such that
// a_i <= c_i, and c_{i+1} = c_i - a_i + b_i, where 0 <= a_i,b_i <= 1000.
// We parameterize by `counts: Vec<i32>` of length n+1 giving the passenger count before each
// stop's exit action (so counts[0] = 0, counts[n] = 0), plus per-stop exits `a` and entries `b`,
// with constraints tying them together.
//
// Simpler approach: just take the user-supplied `exits` and `entries` arrays and verify they satisfy
// all constraints in `requires`.

pub fn generate_candidate(
    exits: Vec<i32>,
    entries: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= exits.len() <= 1000,
        exits.len() == entries.len(),
        forall|i: int| 0 <= i < exits.len() ==> 0 <= #[trigger] exits[i] <= 1000,
        forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
        exits[0] == 0,
        entries[exits.len() - 1] == 0,
        forall|i: int| 0 <= i < exits.len() ==>
            #[trigger] exits@[i] as int <= prefix_passengers(entries@, exits@, i),
    ensures
        ({
            let (e, n) = result;
            &&& 2 <= e.len() <= 1000
            &&& e.len() == n.len()
            &&& forall|i: int| 0 <= i < e.len() ==> 0 <= #[trigger] e[i] <= 1000
            &&& forall|i: int| 0 <= i < n.len() ==> 0 <= #[trigger] n[i] <= 1000
            &&& e[0] == 0
            &&& n[e.len() - 1] == 0
            &&& forall|i: int| 0 <= i < e.len() ==>
                #[trigger] e@[i] as int <= prefix_passengers(n@, e@, i)
        }),
{
    (exits, entries)
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
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(exits: &[i32], entries: &[i32]) -> String {
    let mut s = format!("{}\n", exits.len());
    for i in 0..exits.len() {
        s.push_str(&format!("{} {}\n", exits[i], entries[i]));
    }
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn random_valid(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut exits = vec![0i32; n];
    let mut entries = vec![0i32; n];
    let mut current = 0i32;
    for i in 0..n-1 {
        let a = if i == 0 { 0 } else { rng.gen_range_i32(0, current.min(1000)) };
        current -= a;
        let b = rng.gen_range_i32(0, 1000);
        current += b;
        exits[i] = a;
        entries[i] = b;
    }
    exits[n-1] = current;
    entries[n-1] = 0;
    (exits, entries)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |exits: Vec<i32>, entries: Vec<i32>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= exits.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &exits { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        for &x in &entries { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let (exits, entries) = generate_test_case(exits, entries);
        let inp = build_input(&exits, &entries);
        let ans = Solution::max_passengers(exits, entries);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // pattern variations
    for &n in &[2usize, 3, 5, 10, 50, 100, 500, 1000] {
        // empty-ish: nobody enters
        let mut e = vec![0i32; n]; let mut en = vec![0i32; n];
        en[0] = 1; e[n-1] = 1;
        emit(e, en, &mut seen, &mut out, &mut count);
        // max load at one stop
        if n >= 3 {
            let mut e = vec![0i32; n]; let mut en = vec![0i32; n];
            en[0] = 1000; e[n-1] = 1000;
            emit(e, en, &mut seen, &mut out, &mut count);
        }
        // gradual buildup then exit
        if n >= 2 {
            let mut e = vec![0i32; n]; let mut en = vec![0i32; n];
            for i in 0..n-1 { en[i] = 1000; }
            e[n-1] = ((n - 1) * 1000) as i32;
            emit(e, en, &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 200),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let (e, en) = random_valid(&mut rng, n);
        emit(e, en, &mut seen, &mut out, &mut count);
    }
}
