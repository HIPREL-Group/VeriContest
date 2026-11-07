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


// Spec fn helpers copied from spec.rs

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

// Lemma: appending to exits does not change prefix_sum_exits for indices <= old length
proof fn prefix_sum_exits_append_stable(exits: Seq<i32>, new_val: i32, end: int)
    requires
        0 <= end <= exits.len(),
    ensures
        prefix_sum_exits(exits.push(new_val), end) == prefix_sum_exits(exits, end),
    decreases end,
{
    if end > 0 {
        prefix_sum_exits_append_stable(exits, new_val, end - 1);
        assert(exits.push(new_val)[end - 1] == exits[end - 1]);
    }
}

// Lemma: prefix_sum_entries is non-negative when all entries are non-negative
proof fn prefix_sum_entries_nonneg(entries: Seq<i32>, end: int)
    requires
        0 <= end <= entries.len(),
        forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i],
    ensures
        prefix_sum_entries(entries, end) >= 0,
    decreases end,
{
    if end > 0 {
        prefix_sum_entries_nonneg(entries, end - 1);
    }
}

// Lemma: prefix_sum_entries bounded by 1000 * end
proof fn prefix_sum_entries_bounded(entries: Seq<i32>, end: int)
    requires
        0 <= end <= entries.len(),
        forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
    ensures
        prefix_sum_entries(entries, end) <= 1000 * end,
    decreases end,
{
    if end > 0 {
        prefix_sum_entries_bounded(entries, end - 1);
    }
}

pub fn generate_candidate(
    entries: Vec<i32>,
    exit_caps: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= entries.len() <= 1000,
        entries.len() == exit_caps.len(),
        forall|i: int| 0 <= i < entries.len() ==> 0 <= #[trigger] entries[i] <= 1000,
        forall|i: int| 0 <= i < exit_caps.len() ==> 0 <= #[trigger] exit_caps[i] <= 1000,
        entries[entries.len() - 1] == 0,
    ensures
        2 <= result.0.len() <= 1000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        result.0[0] == 0,
        result.1[result.0.len() - 1] == 0,
        forall|i: int| 0 <= i < result.0.len() ==>
            #[trigger] result.0@[i] as int <= prefix_passengers(result.1@, result.0@, i),
{
    let n = entries.len();
    let mut exits: Vec<i32> = Vec::new();
    let mut current_passengers: i32 = 0;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == entries.len(),
            n == exit_caps.len(),
            2 <= n <= 1000,
            exits.len() == i,
            current_passengers >= 0,
            current_passengers as int == prefix_passengers(entries@, exits@, i as int),
            current_passengers as int <= 1000 * (i as int),
            forall|j: int| 0 <= j < entries.len() ==> 0 <= #[trigger] entries[j] <= 1000,
            forall|j: int| 0 <= j < exit_caps.len() ==> 0 <= #[trigger] exit_caps[j] <= 1000,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] exits[j] <= 1000,
            forall|j: int| 0 <= j < i as int ==>
                #[trigger] exits@[j] as int <= prefix_passengers(entries@, exits@, j),
            i > 0 ==> exits[0] == 0,
            entries[entries.len() - 1] == 0,
        decreases n - i,
    {
        let exit_val: i32 = if i == 0 {
            0i32
        } else if mutation_kind == 1 {
            // No exits: passengers only accumulate
            0i32
        } else if mutation_kind == 2 {
            // Drain as many as possible (capped at 1000 per stop)
            if current_passengers <= 1000 { current_passengers } else { 1000i32 }
        } else if mutation_kind == 3 {
            // Exit 1 passenger at a time (if possible)
            if current_passengers >= 1 { 1i32 } else { 0i32 }
        } else {
            // Default: clamp exit_caps to available passengers
            let cap = exit_caps[i];
            if cap <= current_passengers { cap } else { current_passengers }
        };

        // exit_val is in [0, current_passengers] and [0, 1000]
        assert(0 <= exit_val <= current_passengers);
        assert(exit_val <= 1000);

        let ghost pre_exits = exits@;

        exits.push(exit_val);

        proof {
            // Show prefix_sum_exits is stable after push for all indices <= i
            assert forall|j: int| 0 <= j <= i as int implies
                prefix_sum_exits(exits@, j) == prefix_sum_exits(pre_exits, j)
            by {
                prefix_sum_exits_append_stable(pre_exits, exit_val, j);
            }

            // prefix_passengers is unchanged for indices <= i
            // (prefix_sum_entries doesn't depend on exits, prefix_sum_exits is stable)

            // For the new index i: exits[i] <= prefix_passengers(entries@, exits@, i)
            // prefix_passengers(entries@, exits@, i) == prefix_passengers(entries@, pre_exits, i)
            //   == current_passengers, and exit_val <= current_passengers
        }

        // Update current_passengers for next iteration
        // new current = current - exit_val + entries[i]
        // = prefix_passengers(entries@, exits@, i) - exit_val + entries[i]
        // = prefix_passengers(entries@, exits@, i + 1)

        proof {
            // Unfold one step of prefix_sum_exits at i+1
            assert(prefix_sum_exits(exits@, (i + 1) as int) ==
                   prefix_sum_exits(exits@, i as int) + exits@[i as int] as int);
            // Unfold one step of prefix_sum_entries at i+1
            assert(prefix_sum_entries(entries@, (i + 1) as int) ==
                   prefix_sum_entries(entries@, i as int) + entries@[i as int] as int);
            // Bound on new current_passengers
            prefix_sum_entries_bounded(entries@, (i + 1) as int);
        }

        current_passengers = current_passengers - exit_val + entries[i];

        i += 1;
    }

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
    // a[0]=0, b[n-1]=0, a[i] <= current_pass, total exits = total entries (so empty at end)
    let mut exits = vec![0i32; n];
    let mut entries = vec![0i32; n];
    let mut current = 0i32;
    for i in 0..n {
        let a = if i == 0 { 0 } else { rng.gen_range_i32(0, current.min(1000)) };
        current -= a;
        let b = if i == n-1 { 0 } else { rng.gen_range_i32(0, 1000) };
        current += b;
        exits[i] = a;
        entries[i] = b;
    }
    // Now ensure last stop a_{n-1} = current passengers BEFORE last stop's exits.
    // Currently we set exits[n-1]=0. We need: when arriving at last stop, all exit.
    // So set exits[n-1] = current at that point. We've already adjusted... let me redo.
    // Restart properly: pre-build, then fix last exits.
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
    // last stop: all exit, none enter
    exits[n-1] = current;
    entries[n-1] = 0;
    (exits, entries)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    // Example
    emit(vec![0,2,4,4], vec![3,5,2,0], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![0,0], vec![0,0], &mut seen, &mut out, &mut count);
    emit(vec![0,1], vec![1,0], &mut seen, &mut out, &mut count);
    emit(vec![0,1000], vec![1000,0], &mut seen, &mut out, &mut count);
    emit(vec![0,5,5], vec![3,7,0], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(5, 30),
            3 => rng.gen_range_usize(10, 100),
            _ => rng.gen_range_usize(50, 1000),
        };
        let (e, en) = random_valid(&mut rng, n);
        emit(e, en, &mut seen, &mut out, &mut count);
    }
}
