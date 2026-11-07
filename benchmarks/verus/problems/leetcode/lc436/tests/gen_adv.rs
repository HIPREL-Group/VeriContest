use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: &Vec<i32>,
    offsets: &Vec<i32>,
) -> (intervals: Vec<Vec<i32>>)
    requires
        1 <= starts.len() <= 20_000,
        starts.len() == offsets.len(),
        forall|i: int| 0 <= i < starts.len() ==> -1_000_000 <= #[trigger] starts[i] <= 1_000_000,
        forall|i: int| 0 <= i < offsets.len() ==> 0 <= #[trigger] offsets[i] <= 2_000_000,
        forall|i: int| 0 <= i < starts.len() ==> (#[trigger] starts[i]) as int + (#[trigger] offsets[i]) as int <= 1_000_000,
        forall|i: int, j: int| 0 <= i < j < starts.len() ==> starts[i] != starts[j],
    ensures
        1 <= intervals.len() <= 20_000,
        intervals.len() == starts.len(),
        forall|i: int| 0 <= i < intervals.len() ==> (#[trigger] intervals[i]).len() == 2,
        forall|i: int| 0 <= i < intervals.len() ==> -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
        forall|i: int, j: int| 0 <= i < j < intervals.len() ==> intervals[i][0] != intervals[j][0],
{
    let n = starts.len();
    let mut intervals: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == starts.len(),
            starts.len() == offsets.len(),
            0 <= k <= n,
            intervals.len() == k,
            forall|i: int| 0 <= i < starts.len() ==> -1_000_000 <= #[trigger] starts[i] <= 1_000_000,
            forall|i: int| 0 <= i < offsets.len() ==> 0 <= #[trigger] offsets[i] <= 2_000_000,
            forall|i: int| 0 <= i < starts.len() ==> (#[trigger] starts[i]) as int + (#[trigger] offsets[i]) as int <= 1_000_000,
            forall|i: int, j: int| 0 <= i < j < starts.len() ==> starts[i] != starts[j],
            forall|i: int| 0 <= i < k as int ==> (#[trigger] intervals[i]).len() == 2,
            forall|i: int| 0 <= i < k as int ==> intervals[i][0] == starts[i],
            forall|i: int| 0 <= i < k as int ==> intervals[i][1] as int == starts[i] as int + offsets[i] as int,
            forall|i: int| 0 <= i < k as int ==> -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
        decreases n - k,
    {
        let s = starts[k];
        let o = offsets[k];
        let e: i32 = s + o;
        let mut iv: Vec<i32> = Vec::new();
        iv.push(s);
        iv.push(e);
        assert(iv.len() == 2);
        assert(iv[0] == s);
        assert(iv[1] == e);
        intervals.push(iv);
        k = k + 1;
    }
    assert forall|i: int, j: int| 0 <= i < j < intervals.len() implies intervals[i][0] != intervals[j][0] by {
        assert(intervals[i][0] == starts[i]);
        assert(intervals[j][0] == starts[j]);
        assert(starts[i] != starts[j]);
    }
    intervals
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn unique_starts(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    use std::collections::HashSet;
    let mut seen: HashSet<i32> = HashSet::new();
    let mut out: Vec<i32> = Vec::new();
    let mut attempts = 0usize;
    while out.len() < n && attempts < n * 20 + 100 {
        let v = rng.gen_range_i32(lo, hi);
        if !seen.contains(&v) {
            seen.insert(v);
            out.push(v);
        }
        attempts += 1;
    }
    // fill remaining with sequential unused
    let mut cursor: i32 = lo;
    while out.len() < n {
        if !seen.contains(&cursor) {
            seen.insert(cursor);
            out.push(cursor);
        }
        if cursor >= hi { break; }
        cursor += 1;
    }
    out
}

fn gen_offsets(rng: &mut Rng, starts: &Vec<i32>, mode: usize) -> Vec<i32> {
    let mut offs: Vec<i32> = Vec::with_capacity(starts.len());
    for &s in starts.iter() {
        let max_off = (1_000_000i64 - s as i64).max(0).min(2_000_000) as i32;
        let o = match mode {
            0 => 0,
            1 => if max_off > 0 { 1 } else { 0 },
            2 => max_off,
            3 => max_off / 2,
            4 => rng.gen_range_i32(0, max_off),
            5 => if max_off >= 10 { 10 } else { max_off },
            6 => if max_off >= 100 { rng.gen_range_i32(0, 100.min(max_off)) } else { max_off },
            7 => max_off.min(1_000_000),
            _ => rng.gen_range_i32(0, max_off),
        };
        offs.push(o);
    }
    offs
}

fn build_case(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, Vec<i32>) {
    let (lo, hi) = match mode {
        0 => (-1_000_000, 1_000_000),
        1 => (-1_000_000, -999_000),
        2 => (999_000, 1_000_000),
        3 => (-100, 100),
        4 => (-1_000_000, 1_000_000),
        5 => (0, 1_000_000),
        6 => (-1_000_000, 0),
        7 => (-1_000_000, 1_000_000),
        _ => (-1_000_000, 1_000_000),
    };
    let lo_adj = lo.max(-1_000_000);
    let hi_adj = hi.min(1_000_000);
    let max_unique = (hi_adj as i64 - lo_adj as i64 + 1) as usize;
    let n_use = n.min(max_unique).max(1);
    let starts = unique_starts(rng, n_use, lo_adj, hi_adj);
    let offsets = gen_offsets(rng, &starts, mode);
    (starts, offsets)
}

fn print_json(intervals: &Vec<Vec<i32>>) {
    print!("{{\"intervals\":[");
    for i in 0..intervals.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", intervals[i][0], intervals[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 9usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 10 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 20000,
            7 => rng.gen_range_usize(1, 50),
            8 => rng.gen_range_usize(1, 500),
            _ => rng.gen_range_usize(1, 20000),
        };
        let n = n.max(1).min(20000);
        let (starts, offsets) = build_case(&mut rng, mode, n);
        let intervals = generate_test_case(&starts, &offsets);
        print_json(&intervals);
    }
}