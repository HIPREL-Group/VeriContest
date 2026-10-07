use vstd::prelude::*;

verus! {

pub open spec fn scan_spec(ts: Seq<i32>, duration: int, i: nat, total: int) -> int
    recommends i <= ts.len(),
    decreases ts.len() - i,
{
    if i >= ts.len() {
        total
    } else if i + 1 >= ts.len() {
        total + duration
    } else {
        let gap = (ts[(i + 1) as int] as int) - (ts[i as int] as int);
        let contrib = if gap < duration { gap } else { duration };
        scan_spec(ts, duration, i + 1, total + contrib)
    }
}

pub open spec fn find_poisoned_duration_spec(ts: Seq<i32>, duration: int) -> int {
    if ts.len() == 0 { 0 } else { scan_spec(ts, duration, 0, 0) }
}


proof fn scan_span_bound(ts: Seq<i32>, duration: int, i: nat, total: int)
    requires i < ts.len(), duration >= 0,
    ensures scan_spec(ts, duration, i, total) <= total + ts[ts.len() - 1] - ts[i as int] + duration,
    decreases ts.len() - i,
{
    if i + 1 < ts.len() {
        let gap = ts[(i + 1) as int] - ts[i as int];
        let contrib = if gap < duration { gap } else { duration };
        scan_span_bound(ts, duration, i + 1, total + contrib);
    }
}
pub fn generate_test_case(raw: Vec<i32>, duration: i32) -> (result: (Vec<i32>, i32))
    ensures 1 <= result.0.len() <= 10000, 0 <= result.1 <= 10000000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10000000,
        forall|i: int| 0 <= i < result.0.len() - 1 ==> #[trigger] result.0[i] <= result.0[i + 1],
        find_poisoned_duration_spec(result.0@, result.1 as int) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10000 { 10000usize } else { raw.len() };
    let duration = if duration < 0 { 0 } else if duration > 10000000 { 10000000 } else { duration };
    let mut ts: Vec<i32> = Vec::new();
    let mut previous = 0i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 10000, ts.len() == i, 0 <= previous <= 10000000,
            i > 0 ==> previous == ts[i - 1],
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] ts[j] <= 10000000,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] ts[j] <= ts[j + 1],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { previous };
        let v = if v < previous { previous } else if v > 10000000 { 10000000 } else { v };
        ts.push(v); previous = v; i += 1;
    }
    proof { scan_span_bound(ts@, duration as int, 0, 0); }
    (ts, duration)
}


pub fn generate_candidate(
    base: i32,
    increments: &Vec<i32>,
    duration: i32,
) -> (res: (Vec<i32>, i32))
    requires
        0 <= base <= 10_000_000,
        0 <= duration <= 10_000_000,
        1 <= increments.len() + 1 <= 10_000,
        forall|i: int| 0 <= i < increments.len() ==> 0 <= #[trigger] increments[i],
        // The cumulative sum must stay <= 10_000_000 - base
        forall|i: int| 0 <= i < increments.len() ==>
            (#[trigger] increments[i]) as int <= 10_000_000 - base as int,
        // Increments themselves bounded
        forall|i: int| 0 <= i < increments.len() ==> #[trigger] increments[i] <= 10_000_000,
        // Monotone: each next increment >= previous increment
        forall|i: int| 0 <= i < increments.len() - 1 ==>
            #[trigger] increments[i] <= increments[i + 1],
    ensures
        ({
            let (ts, dur) = res;
            &&& 1 <= ts.len() <= 10_000
            &&& 0 <= dur <= 10_000_000
            &&& dur == duration
            &&& ts.len() == increments.len() + 1
            &&& forall|j: int| 0 <= j < ts@.len() ==> 0 <= #[trigger] ts@[j] <= 10_000_000i32
            &&& forall|j: int| 0 <= j < ts@.len() - 1 ==>
                    #[trigger] ts@[j] <= ts@[j + 1]
        }),
{
    let mut ts: Vec<i32> = Vec::new();
    ts.push(base);

    let n = increments.len();
    let mut k: usize = 0;

    while k < n
        invariant
            n == increments.len(),
            0 <= k <= n,
            ts.len() == k + 1,
            ts@[0] == base,
            0 <= base <= 10_000_000,
            forall|i: int| 0 <= i < increments.len() ==> 0 <= #[trigger] increments[i],
            forall|i: int| 0 <= i < increments.len() ==>
                (#[trigger] increments[i]) as int <= 10_000_000 - base as int,
            forall|i: int| 0 <= i < increments.len() ==> #[trigger] increments[i] <= 10_000_000,
            forall|i: int| 0 <= i < increments.len() - 1 ==>
                #[trigger] increments[i] <= increments[i + 1],
            forall|j: int| 0 <= j < ts@.len() ==> 0 <= #[trigger] ts@[j] <= 10_000_000i32,
            forall|j: int| 1 <= j < ts@.len() ==> ts@[j] == base + increments@[j - 1],
            forall|j: int| 0 <= j < ts@.len() - 1 ==> #[trigger] ts@[j] <= ts@[j + 1],
        decreases n - k,
    {
        let inc = increments[k];
        let val: i32 = base + inc;
        assert(0 <= val);
        assert(val <= 10_000_000);
        ts.push(val);

        proof {
            // Maintain monotonicity
            if k >= 1 {
                // previous ts[k] == base + increments[k-1], new ts[k+1] == base + increments[k]
                assert(increments@[k as int - 1] <= increments@[k as int]);
            }
        }

        k = k + 1;
    }

    (ts, duration)
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

    fn gen_range(&mut self, lo: i64, hi: i64) -> i64 {
        if lo >= hi {
            return lo;
        }
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
}

fn build_increments(rng: &mut Rng, n: usize, max_inc: i32, mode_monotone: bool) -> Vec<i32> {
    // n is the number of increments (length-1 of timeseries)
    // Need nondecreasing increments
    let mut v: Vec<i32> = Vec::with_capacity(n);
    if n == 0 {
        return v;
    }
    // generate n raw values, then sort
    let mut raw: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let x = rng.gen_range(0, max_inc as i64) as i32;
        raw.push(x);
    }
    if mode_monotone {
        raw.sort();
    } else {
        raw.sort();
    }
    for x in raw {
        v.push(x);
    }
    v
}

fn gen_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, Vec<i32>, i32) {
    // Returns (base, increments, duration) such that base + max_inc <= 10_000_000
    match mode {
        0 => {
            // Small random
            let n = rng.gen_range(1, 10) as usize;
            let duration = rng.gen_range(0, 10) as i32;
            let base = rng.gen_range(0, 100) as i32;
            let max_inc = 100i32;
            let incs = build_increments(rng, n - 1, max_inc, true);
            (base, incs, duration)
        }
        1 => {
            // duration = 0
            let n = rng.gen_range(1, 100) as usize;
            let base = rng.gen_range(0, 1000) as i32;
            let incs = build_increments(rng, n - 1, 1000, true);
            (base, incs, 0)
        }
        2 => {
            // duration = max
            let n = rng.gen_range(1, 100) as usize;
            let base = 0i32;
            let max_inc = 10_000_000i32;
            let incs = build_increments(rng, n - 1, max_inc, true);
            (base, incs, 10_000_000)
        }
        3 => {
            // All same time series values (zero increments)
            let n = rng.gen_range(1, 1000) as usize;
            let base = rng.gen_range(0, 10_000_000) as i32;
            let mut incs: Vec<i32> = Vec::with_capacity(n - 1);
            for _ in 0..(n - 1) {
                incs.push(0);
            }
            let duration = rng.gen_range(0, 10_000_000) as i32;
            (base, incs, duration)
        }
        4 => {
            // Single element
            let base = rng.gen_range(0, 10_000_000) as i32;
            let duration = rng.gen_range(0, 10_000_000) as i32;
            (base, Vec::new(), duration)
        }
        5 => {
            // Large n = 10000
            let n = 10_000usize;
            let base = 0i32;
            let max_inc = 1000i32;
            let incs = build_increments(rng, n - 1, max_inc, true);
            let duration = rng.gen_range(0, 1000) as i32;
            (base, incs, duration)
        }
        6 => {
            // Gaps exactly equal to duration
            let n = rng.gen_range(2, 100) as usize;
            let duration = rng.gen_range(1, 1000) as i32;
            let base = 0i32;
            let mut incs: Vec<i32> = Vec::with_capacity(n - 1);
            for i in 0..(n - 1) {
                let v = duration.saturating_mul((i + 1) as i32);
                if v > 10_000_000 {
                    incs.push(10_000_000);
                } else {
                    incs.push(v);
                }
            }
            // ensure nondecreasing - they are by construction, but clamp can break monotonicity
            // sort to be safe
            incs.sort();
            (base, incs, duration)
        }
        7 => {
            // Gaps of 1
            let n = rng.gen_range(2, 1000) as usize;
            let base = 0i32;
            let mut incs: Vec<i32> = Vec::with_capacity(n - 1);
            for i in 0..(n - 1) {
                let v = (i + 1) as i32;
                incs.push(v);
            }
            let duration = rng.gen_range(1, 100) as i32;
            (base, incs, duration)
        }
        8 => {
            // Base near max
            let base = rng.gen_range(9_000_000, 10_000_000) as i32;
            let n = rng.gen_range(1, 100) as usize;
            let max_inc = 10_000_000 - base;
            let incs = build_increments(rng, n - 1, max_inc, true);
            let duration = rng.gen_range(0, 10_000_000) as i32;
            (base, incs, duration)
        }
        9 => {
            // Overlapping attacks: all same time
            let n = rng.gen_range(2, 100) as usize;
            let base = rng.gen_range(0, 10_000_000) as i32;
            let mut incs: Vec<i32> = Vec::with_capacity(n - 1);
            for _ in 0..(n - 1) {
                incs.push(0);
            }
            let duration = rng.gen_range(1, 1000) as i32;
            (base, incs, duration)
        }
        _ => {
            let n = rng.gen_range(1, 500) as usize;
            let base = rng.gen_range(0, 1_000_000) as i32;
            let max_inc = 10_000_000 - base;
            let max_inc_use = if max_inc > 1_000_000 { 1_000_000 } else { max_inc };
            let incs = build_increments(rng, n - 1, max_inc_use, true);
            let duration = rng.gen_range(0, 1_000_000) as i32;
            (base, incs, duration)
        }
    }
}

fn validate_and_fix(base: i32, incs: Vec<i32>) -> (i32, Vec<i32>) {
    // Ensure all preconditions hold: 0 <= base <= 10_000_000, each inc >= 0, inc <= 10_000_000 - base, and nondecreasing
    let b = if base < 0 { 0 } else if base > 10_000_000 { 10_000_000 } else { base };
    let max_inc = 10_000_000 - b;
    let mut fixed: Vec<i32> = Vec::with_capacity(incs.len());
    for x in incs {
        let v = if x < 0 { 0 } else if x > max_inc { max_inc } else { x };
        fixed.push(v);
    }
    // sort for monotonicity
    fixed.sort();
    (b, fixed)
}

fn print_json(ts: &[i32], duration: i32) {
    let (ts, duration) = generate_test_case(ts.to_vec(), duration);
    print!("{{\"time_series\":[");
    for i in 0..ts.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", ts[i]);
    }
    println!("],\"duration\":{}}}", duration);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (base, incs, duration) = gen_case(&mut rng, mode, t);
        let (base, incs) = validate_and_fix(base, incs);
        let dur = if duration < 0 { 0 } else if duration > 10_000_000 { 10_000_000 } else { duration };
        let (ts, d) = generate_candidate(base, &incs, dur);
        print_json(&ts, d);
    }
}
