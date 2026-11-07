use vstd::prelude::*;

verus! {

pub open spec fn valid_schedule(starts: Seq<i32>, ends: Seq<i32>) -> bool {
    1 <= starts.len() <= 50 && starts.len() == ends.len()
        && forall|i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i] < #[trigger] ends[i] <= 1000
        && forall|i: int| 0 <= i < starts.len() - 1 ==> #[trigger] ends[i] < starts[i + 1]
}
fn construct_schedule(raw_starts: Vec<i32>, raw_ends: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures valid_schedule(result.0@, result.1@),
{
    let n = if raw_starts.len() < 1 { 1usize } else if raw_starts.len() > 50 { 50usize } else { raw_starts.len() };
    let mut starts: Vec<i32> = Vec::new();
    let mut ends: Vec<i32> = Vec::new();
    let mut i = 0usize;
    let mut previous = -1i32;
    while i < n
        invariant i <= n, 1 <= n <= 50, starts.len() == i, ends.len() == i,
            -1 <= previous <= 1000 - 2 * (n - i),
            i == 0 ==> previous == -1,
            i > 0 ==> previous == ends[i - 1],
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] starts[j],
            forall|j: int| 0 <= j < i ==> #[trigger] ends[j] <= 1000,
            forall|j: int| 0 <= j < i ==> starts[j] < #[trigger] ends[j],
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] ends[j] < starts[j + 1],
        decreases n - i,
    {
        let low = previous + 1;
        let high = 1000 - 2 * ((n - i) as i32) + 1;
        let a = if i < raw_starts.len() { raw_starts[i] } else { low };
        let a = if a < low { low } else if a > high { high } else { a };
        let high = high + 1;
        let b = if i < raw_ends.len() { raw_ends[i] } else { a + 1 };
        let b = if b <= a { a + 1 } else if b > high { high } else { b };
        let ghost old_starts = starts@;
        let ghost old_ends = ends@;
        starts.push(a);
        ends.push(b);
        assert forall|j: int| 0 <= j < starts.len() implies
            0 <= #[trigger] starts[j] < #[trigger] ends[j] <= 1000 by {
            if j < i { assert(0 <= old_starts[j] < old_ends[j] <= 1000); }
        }
        previous = b;
        i += 1;
    }
    (starts, ends)
}
pub fn generate_test_case(zs: Vec<i32>, ze: Vec<i32>, xs: Vec<i32>, xe: Vec<i32>, l: i32, r: i32)
    -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>, i32, i32))
    ensures valid_schedule(result.0@, result.1@), valid_schedule(result.2@, result.3@),
        0 <= result.4 <= result.5 <= 1000,
{
    let (zs, ze) = construct_schedule(zs, ze);
    let (xs, xe) = construct_schedule(xs, xe);
    let l = if l < 0 { 0 } else if l > 1000 { 1000 } else { l };
    let r = if r < l { l } else if r > 1000 { 1000 } else { r };
    (zs, ze, xs, xe, l, r)
}


pub open spec fn candidate_valid_schedule(starts: Seq<i32>, ends: Seq<i32>) -> bool {
    1 <= starts.len() <= 50
        && starts.len() == ends.len()
        && forall|i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i] < #[trigger] ends[i] <= 1000
}

pub fn generate_candidate(
    z_starts: Vec<i32>,
    z_deltas: Vec<i32>,
    x_starts: Vec<i32>,
    x_deltas: Vec<i32>,
    l: i32,
    r: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>, i32, i32))
    requires
        1 <= z_starts.len() <= 50,
        z_starts.len() == z_deltas.len(),
        forall|i: int| 0 <= i < z_starts.len() ==> 0 <= #[trigger] z_starts[i] <= 999,
        forall|i: int| 0 <= i < z_deltas.len() ==> 1 <= #[trigger] z_deltas[i] && z_starts[i] + z_deltas[i] <= 1000,
        1 <= x_starts.len() <= 50,
        x_starts.len() == x_deltas.len(),
        forall|i: int| 0 <= i < x_starts.len() ==> 0 <= #[trigger] x_starts[i] <= 999,
        forall|i: int| 0 <= i < x_deltas.len() ==> 1 <= #[trigger] x_deltas[i] && x_starts[i] + x_deltas[i] <= 1000,
        0 <= l <= r <= 1000,
    ensures
        candidate_valid_schedule(result.0@, result.1@),
        candidate_valid_schedule(result.2@, result.3@),
        0 <= result.4 <= result.5 <= 1000,
{
    // Build z_ends from z_starts + z_deltas
    let mut z_ends: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < z_starts.len()
        invariant
            0 <= i <= z_starts.len(),
            z_ends.len() == i,
            z_starts.len() == z_deltas.len(),
            1 <= z_starts.len() <= 50,
            forall|k: int| 0 <= k < z_starts.len() ==> 0 <= #[trigger] z_starts[k] <= 999,
            forall|k: int| 0 <= k < z_deltas.len() ==> 1 <= #[trigger] z_deltas[k] && z_starts[k] + z_deltas[k] <= 1000,
            forall|k: int| 0 <= k < i ==> 0 <= z_starts[k] < #[trigger] z_ends[k] <= 1000,
        decreases z_starts.len() - i,
    {
        z_ends.push(z_starts[i] + z_deltas[i]);
        i += 1;
    }

    // Build x_ends from x_starts + x_deltas
    let mut x_ends: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < x_starts.len()
        invariant
            0 <= j <= x_starts.len(),
            x_ends.len() == j,
            x_starts.len() == x_deltas.len(),
            1 <= x_starts.len() <= 50,
            forall|k: int| 0 <= k < x_starts.len() ==> 0 <= #[trigger] x_starts[k] <= 999,
            forall|k: int| 0 <= k < x_deltas.len() ==> 1 <= #[trigger] x_deltas[k] && x_starts[k] + x_deltas[k] <= 1000,
            forall|k: int| 0 <= k < j ==> 0 <= x_starts[k] < #[trigger] x_ends[k] <= 1000,
        decreases x_starts.len() - j,
    {
        x_ends.push(x_starts[j] + x_deltas[j]);
        j += 1;
    }

    // Scalar mutations on l, r
    let (ml, mr) = if mutation_kind == 0 {
        (l, r)                      // identity
    } else if mutation_kind == 1 {
        (l, l)                      // single point at l
    } else if mutation_kind == 2 {
        (r, r)                      // single point at r
    } else if mutation_kind == 3 {
        (0i32, r)                   // l at minimum
    } else if mutation_kind == 4 {
        (l, 1000i32)                // r at maximum
    } else if mutation_kind == 5 {
        (0i32, 1000i32)             // full range
    } else if mutation_kind == 6 {
        (0i32, 0i32)                // both zero
    } else {
        (l, r)                      // fallback
    };

    assert(candidate_valid_schedule(z_starts@, z_ends@));
    assert(candidate_valid_schedule(x_starts@, x_ends@));

    (z_starts, z_ends, x_starts, x_ends, ml, mr)
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

fn build_input(p: usize, q: usize, l: i32, r: i32, z_starts: &[i32], z_ends: &[i32], x_starts: &[i32], x_ends: &[i32]) -> String {
    let mut s = format!("{} {} {} {}\n", p, q, l, r);
    for i in 0..p {
        s.push_str(&format!("{} {}\n", z_starts[i], z_ends[i]));
    }
    for i in 0..q {
        s.push_str(&format!("{} {}\n", x_starts[i], x_ends[i]));
    }
    s
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn random_schedule(rng: &mut Rng, count: usize) -> (Vec<i32>, Vec<i32>) {
    // Each segment has 0 <= a < b <= 1000; consecutive segments don't overlap
    let mut starts = Vec::new();
    let mut ends = Vec::new();
    let mut last_end: i64 = -1;
    for _ in 0..count {
        if last_end + 2 > 1000 { break; }
        let a = rng.gen_range_i64(last_end + 1, last_end + 2.max(1).min(1000 - last_end));
        let a = a.max(last_end + 1).min(1000);
        let b = rng.gen_range_i64(a + 1, (a + 50).min(1000));
        starts.push(a as i32);
        ends.push(b as i32);
        last_end = b;
    }
    if starts.is_empty() {
        starts.push(0);
        ends.push(1);
    }
    (starts, ends)
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(469);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |z_starts: Vec<i32>, z_ends: Vec<i32>, x_starts: Vec<i32>, x_ends: Vec<i32>, l: i32, r: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (z_starts, z_ends, x_starts, x_ends, l, r) = generate_test_case(z_starts, z_ends, x_starts, x_ends, l, r);
        if *count >= target_count { return; }
        let p = z_starts.len();
        let q = x_starts.len();
        if p == 0 || q == 0 { return; }
        if l > r { return; }
        let key = format!("{:?}_{:?}_{:?}_{:?}_{}_{}", z_starts, z_ends, x_starts, x_ends, l, r);
        if !seen.insert(key) { return; }
        let result = Solution::count_chat_times(z_starts.clone(), z_ends.clone(), x_starts.clone(), x_ends.clone(), l, r);
        let inp = build_input(p, q, l, r, &z_starts, &z_ends, &x_starts, &x_ends);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![2], vec![3], vec![0], vec![1], 0, 4, &mut seen, &mut out, &mut count);
    emit(vec![15, 23], vec![17, 26], vec![1, 7, 15], vec![4, 11, 17], 0, 20, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![0], vec![1000], vec![0], vec![1000], 0, 0, &mut seen, &mut out, &mut count);
    emit(vec![0], vec![1], vec![999], vec![1000], 0, 1000, &mut seen, &mut out, &mut count);
    emit(vec![500], vec![500], vec![500], vec![500], 0, 1000, &mut seen, &mut out, &mut count);

    // Random
    while count < target_count {
        let p = rng.gen_range_usize(1, 50);
        let q = rng.gen_range_usize(1, 50);
        let (z_starts, z_ends) = random_schedule(&mut rng, p);
        let (x_starts, x_ends) = random_schedule(&mut rng, q);
        let l = rng.gen_range_i64(0, 1000) as i32;
        let r_val = rng.gen_range_i64(l as i64, 1000) as i32;
        emit(z_starts, z_ends, x_starts, x_ends, l, r_val, &mut seen, &mut out, &mut count);
    }
}
