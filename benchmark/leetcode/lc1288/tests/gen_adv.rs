use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: &Vec<i32>,
    lengths: &Vec<i32>,
) -> (intervals: Vec<Vec<i32>>)
    requires
        starts.len() == lengths.len(),
        1 <= starts.len() <= 1000,
        forall|i: int| 0 <= i < starts.len() ==>
            0 <= #[trigger] starts[i] <= 99_999,
        forall|i: int| 0 <= i < lengths.len() ==>
            1 <= #[trigger] lengths[i] <= 100_000,
        forall|i: int| 0 <= i < starts.len() ==>
            (#[trigger] starts[i]) as int + (#[trigger] lengths[i]) as int <= 100_000,
        forall|i: int, j: int| 0 <= i < j < starts.len() ==>
            !(#[trigger] starts[i] == #[trigger] starts[j] && #[trigger] lengths[i] == #[trigger] lengths[j]),
    ensures
        1 <= intervals.len() <= 1000,
        forall|i: int| 0 <= i < intervals.len() ==>
            (#[trigger] intervals[i]).len() == 2,
        forall|i: int| 0 <= i < intervals.len() ==>
            0 <= (#[trigger] intervals[i])[0] < intervals[i][1] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < intervals.len() ==>
            !(intervals[i][0] == intervals[j][0] && intervals[i][1] == intervals[j][1]),
{
    let n = starts.len();
    let mut intervals: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            n == starts.len(),
            starts.len() == lengths.len(),
            1 <= n <= 1000,
            k <= n,
            intervals.len() == k,
            forall|i: int| 0 <= i < starts.len() ==>
                0 <= #[trigger] starts[i] <= 99_999,
            forall|i: int| 0 <= i < lengths.len() ==>
                1 <= #[trigger] lengths[i] <= 100_000,
            forall|i: int| 0 <= i < starts.len() ==>
                (#[trigger] starts[i]) as int + (#[trigger] lengths[i]) as int <= 100_000,
            forall|i: int, j: int| 0 <= i < j < starts.len() ==>
                !(#[trigger] starts[i] == #[trigger] starts[j] && #[trigger] lengths[i] == #[trigger] lengths[j]),
            forall|i: int| 0 <= i < k as int ==>
                (#[trigger] intervals[i]).len() == 2,
            forall|i: int| 0 <= i < k as int ==>
                (#[trigger] intervals[i])[0] == starts[i],
            forall|i: int| 0 <= i < k as int ==>
                (#[trigger] intervals[i])[1] == (starts[i] as int + lengths[i] as int) as i32,
            forall|i: int| 0 <= i < k as int ==>
                0 <= (#[trigger] intervals[i])[0] < intervals[i][1] <= 100_000,
        decreases n - k,
    {
        let s = starts[k];
        let l = lengths[k];
        let e: i32 = s + l;
        let mut v: Vec<i32> = Vec::new();
        v.push(s);
        v.push(e);
        assert(v.len() == 2);
        assert(v[0] == s);
        assert(v[1] == e);
        intervals.push(v);
        k = k + 1;
    }

    proof {
        assert forall|i: int, j: int| 0 <= i < j < intervals.len() implies
            !(intervals[i][0] == intervals[j][0] && intervals[i][1] == intervals[j][1])
        by {
            if intervals[i][0] == intervals[j][0] && intervals[i][1] == intervals[j][1] {
                assert(starts[i] == starts[j]);
                assert(intervals[i][1] as int == starts[i] as int + lengths[i] as int);
                assert(intervals[j][1] as int == starts[j] as int + lengths[j] as int);
                assert(lengths[i] == lengths[j]);
                assert(false);
            }
        }
    }

    intervals
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

use std::collections::HashSet;

fn build(starts: Vec<i32>, lengths: Vec<i32>) -> Option<(Vec<i32>, Vec<i32>)> {
    if starts.len() != lengths.len() { return None; }
    if starts.is_empty() || starts.len() > 1000 { return None; }
    let mut set: HashSet<(i32, i32)> = HashSet::new();
    for i in 0..starts.len() {
        if starts[i] < 0 || starts[i] > 99_999 { return None; }
        if lengths[i] < 1 || lengths[i] > 100_000 { return None; }
        if starts[i] as i64 + lengths[i] as i64 > 100_000 { return None; }
        if !set.insert((starts[i], lengths[i])) { return None; }
    }
    Some((starts, lengths))
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    loop {
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => rng.gen_usize(1, 10),
            3 => rng.gen_usize(50, 200),
            4 => 1000,
            5 => rng.gen_usize(1, 1000),
            6 => rng.gen_usize(2, 20),
            7 => rng.gen_usize(2, 30),
            8 => rng.gen_usize(2, 50),
            _ => rng.gen_usize(1, 500),
        };
        let mut starts = Vec::new();
        let mut lengths = Vec::new();
        let mut used: HashSet<(i32, i32)> = HashSet::new();
        let mut attempts = 0;
        while starts.len() < n && attempts < n * 20 + 50 {
            attempts += 1;
            let (s, l) = match mode {
                6 => {
                    // nested: all contain a common interval
                    let mid = 50_000;
                    let half = rng.gen_range(1, 49_000);
                    (mid - half, 2 * half)
                }
                7 => {
                    // chain starting at 0
                    let l = rng.gen_range(1, 100_000);
                    (0, l)
                }
                8 => {
                    // same length, different starts
                    let l = 100;
                    let s = rng.gen_range(0, 99_900);
                    (s, l)
                }
                4 | 5 => {
                    let s = rng.gen_range(0, 99_999);
                    let maxl = 100_000 - s;
                    let l = rng.gen_range(1, maxl);
                    (s, l)
                }
                _ => {
                    let s = rng.gen_range(0, 99_999);
                    let maxl = 100_000 - s;
                    let l = rng.gen_range(1, maxl.min(1000).max(1));
                    (s, l)
                }
            };
            if s < 0 || s > 99_999 { continue; }
            if l < 1 { continue; }
            if s as i64 + l as i64 > 100_000 { continue; }
            if used.insert((s, l)) {
                starts.push(s);
                lengths.push(l);
            }
        }
        if starts.is_empty() {
            starts.push(0);
            lengths.push(1);
        }
        if let Some(x) = build(starts, lengths) {
            return x;
        }
    }
}

fn print_json(intervals: &[Vec<i32>]) {
    print!("{{\"intervals\":[");
    for i in 0..intervals.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", intervals[i][0], intervals[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;
    for t in 0..total {
        let mode = t % modes;
        let (starts, lengths) = gen_mode(&mut rng, mode);
        let starts_v = starts.clone();
        let lengths_v = lengths.clone();
        let intervals = generate_test_case(&starts_v, &lengths_v);
        print_json(&intervals);
    }
}