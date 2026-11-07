use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    gaps: &Vec<i32>,
    dist: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= start <= 1_000_000_000,
        1 <= dist <= 1_000_000_000,
        gaps.len() + 1 <= 100_000,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i],
        // Bound sum so it stays <= 1_000_000_000
        // We ensure by requiring start + sum(gaps) <= 1_000_000_000 via a simple check:
        // Use a strict per-step bound: start plus cumulative gaps must be <= 1_000_000_000.
        // We express this via requiring the last value computed is <= 1e9.
        // To keep it simple: require gaps[i] <= some bound and gaps.len() * bound + start <= 1e9.
        // We'll require gaps.len() <= 99_999 and each gap <= 9_999 and start <= 1_000.
        // Actually use explicit cumulative bound:
        forall|i: int| 0 <= i < gaps.len() ==> #[trigger] gaps[i] <= 9_000,
        gaps.len() <= 99_999,
        start <= 10_000,
    ensures
        ({
            let (rungs, d) = res;
            &&& 1 <= rungs.len() <= 100_000
            &&& forall|i: int| 0 <= i < rungs.len() ==> 1 <= #[trigger] rungs[i] <= 1_000_000_000
            &&& 1 <= d <= 1_000_000_000
            &&& forall|i: int, j: int| 0 <= i < j < rungs.len() ==> rungs[i] < rungs[j]
            &&& d == dist
        }),
{
    let mut rungs: Vec<i32> = Vec::new();
    rungs.push(start);

    let n = gaps.len();
    let mut idx: usize = 0;
    let mut cur: i32 = start;

    while idx < n
        invariant
            idx <= n,
            n == gaps.len(),
            rungs.len() == idx + 1,
            rungs[0] == start,
            1 <= start <= 10_000,
            cur <= 10_000 + 9_000 * (idx as int),
            cur >= start,
            rungs[idx as int] == cur,
            forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 9_000,
            gaps.len() <= 99_999,
            forall|i: int| 0 <= i < rungs.len() ==> 1 <= #[trigger] rungs[i],
            forall|i: int| 0 <= i < rungs.len() ==> #[trigger] rungs[i] <= cur,
            forall|i: int, j: int| 0 <= i < j < rungs.len() ==> rungs[i] < rungs[j],
        decreases n - idx,
    {
        let g = gaps[idx];
        assert(g >= 1);
        assert(g <= 9_000);
        let new_cur = cur + g;
        proof {
            assert(cur <= 10_000 + 9_000 * (idx as int));
            assert(new_cur <= 10_000 + 9_000 * (idx as int) + 9_000);
            assert(new_cur <= 10_000 + 9_000 * ((idx + 1) as int));
        }
        rungs.push(new_cur);
        cur = new_cur;
        idx = idx + 1;
    }

    proof {
        assert(cur <= 10_000 + 9_000 * (n as int));
        assert(n <= 99_999);
        assert(9_000 * (n as int) <= 9_000 * 99_999);
        assert(cur <= 1_000_000_000);
        assert forall|i: int| 0 <= i < rungs.len() implies #[trigger] rungs[i] <= 1_000_000_000 by {
            assert(rungs[i] <= cur);
        }
        assert(rungs.len() == n + 1);
        assert(rungs.len() <= 100_000);
        assert(rungs.len() >= 1);
    }

    (rungs, dist)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build(start: i32, gaps_vec: Vec<i32>, dist: i32) -> (Vec<i32>, i32) {
    generate_test_case(start, &gaps_vec, dist)
}

fn print_case(rungs: &[i32], dist: i32) {
    print!("{{\"rungs\":[");
    for i in 0..rungs.len() {
        if i > 0 { print!(","); }
        print!("{}", rungs[i]);
    }
    println!("],\"dist\":{}}}", dist);
}

fn adversarial(rng: &mut Rng, mode: usize) -> (i32, Vec<i32>, i32) {
    match mode {
        0 => {
            // small: single rung
            let start = rng.gen_range_i32(1, 10_000);
            let dist = rng.gen_range_i32(1, 1_000_000_000);
            (start, Vec::new(), dist)
        }
        1 => {
            // dist = 1, forces many inserts
            let start = rng.gen_range_i32(1, 10_000);
            let n = rng.gen_range_usize(0, 200);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            (start, gaps, 1)
        }
        2 => {
            // large dist, no inserts needed
            let start = rng.gen_range_i32(1, 10_000);
            let n = rng.gen_range_usize(0, 500);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            (start, gaps, 1_000_000_000)
        }
        3 => {
            // gaps exactly equal to dist
            let dist = rng.gen_range_i32(1, 9_000);
            let start = dist;
            let n = rng.gen_range_usize(0, 300);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(dist); }
            (start, gaps, dist)
        }
        4 => {
            // gaps exactly dist+1 (off-by-one edge)
            let dist = rng.gen_range_i32(1, 8_999);
            let start = dist + 1;
            let n = rng.gen_range_usize(0, 200);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(dist + 1); }
            (start.min(10_000), gaps, dist)
        }
        5 => {
            // start very large, dist small
            let start: i32 = 10_000;
            let n = rng.gen_range_usize(0, 500);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            let dist = rng.gen_range_i32(1, 100);
            (start, gaps, dist)
        }
        6 => {
            // start = 1
            let n = rng.gen_range_usize(0, 1000);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            let dist = rng.gen_range_i32(1, 1_000_000_000);
            (1, gaps, dist)
        }
        7 => {
            // maximum length
            let start = rng.gen_range_i32(1, 10_000);
            let n = 99_999usize;
            let mut gaps = Vec::with_capacity(n);
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            let dist = rng.gen_range_i32(1, 1_000_000_000);
            (start, gaps, dist)
        }
        8 => {
            // all minimal gaps of 1
            let start = rng.gen_range_i32(1, 10_000);
            let n = rng.gen_range_usize(0, 5_000);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(1); }
            let dist = rng.gen_range_i32(1, 1_000_000_000);
            (start, gaps, dist)
        }
        9 => {
            // start equals dist exactly
            let dist = rng.gen_range_i32(1, 10_000);
            let start = dist;
            let n = rng.gen_range_usize(0, 500);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            (start, gaps, dist)
        }
        _ => {
            // random
            let start = rng.gen_range_i32(1, 10_000);
            let n = rng.gen_range_usize(0, 1000);
            let mut gaps = Vec::new();
            for _ in 0..n { gaps.push(rng.gen_range_i32(1, 9_000)); }
            let dist = rng.gen_range_i32(1, 1_000_000_000);
            (start, gaps, dist)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (start, gaps, dist) = adversarial(&mut rng, mode);
        let (rungs, d) = build(start, gaps, dist);
        print_case(&rungs, d);
    }
}