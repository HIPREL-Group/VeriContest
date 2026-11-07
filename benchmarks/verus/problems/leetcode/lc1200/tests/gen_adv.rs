use vstd::prelude::*;

verus! {

pub fn generate_test_case(base: i32, n: usize, offsets: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        2 <= n <= 100_000,
        offsets.len() == n,
        // base + offsets[i] in range
        -500_000 <= base <= 500_000,
        forall |i: int| 0 <= i < offsets.len() ==>
            -500_000 <= #[trigger] offsets[i] <= 500_000,
        // all offsets distinct
        forall |i: int, j: int| 0 <= i < j < offsets.len() ==>
            offsets[i] != offsets[j],
    ensures
        2 <= arr.len() <= 100_000,
        arr.len() == n,
        forall |i: int| 0 <= i < arr.len() ==> -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == offsets.len(),
            arr.len() == i,
            -500_000 <= base <= 500_000,
            forall |k: int| 0 <= k < offsets.len() ==>
                -500_000 <= #[trigger] offsets[k] <= 500_000,
            forall |k: int, m: int| 0 <= k < m < offsets.len() ==>
                offsets[k] != offsets[m],
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] arr[k] == base as int + offsets[k] as int,
            forall |k: int| 0 <= k < i as int ==>
                -1_000_000 <= #[trigger] arr[k] <= 1_000_000,
        decreases n - i,
    {
        let v: i32 = base + offsets[i];
        proof {
            assert(base as int + offsets[i as int] as int <= 500_000 + 500_000);
            assert(base as int + offsets[i as int] as int >= -500_000 - 500_000);
        }
        arr.push(v);
        i = i + 1;
    }

    proof {
        assert forall |p: int, q: int| 0 <= p < q < arr.len() implies arr[p] != arr[q] by {
            assert(arr[p] == base as int + offsets[p] as int);
            assert(arr[q] == base as int + offsets[q] as int);
            assert(offsets[p] != offsets[q]);
        }
    }

    arr
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

// Generate a permutation of distinct offsets in [-500_000, 500_000]
// with |offsets| = n, and then build arr = base + offsets[i].
// We carefully keep values bounded.

fn distinct_offsets_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    use std::collections::HashSet;
    let mut set: HashSet<i32> = HashSet::new();
    let mut out: Vec<i32> = Vec::new();
    let range = (hi as i64 - lo as i64 + 1) as usize;
    assert!(range >= n);
    while out.len() < n {
        let v = rng.gen_range_i32(lo, hi);
        if set.insert(v) {
            out.push(v);
        }
    }
    out
}

fn distinct_offsets_consecutive(start: i32, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    // consecutive integers starting from start (clamped so they fit)
    let mut s = start;
    if (s as i64) + (n as i64) - 1 > hi as i64 {
        s = hi - (n as i32) + 1;
    }
    if s < lo {
        s = lo;
    }
    let mut out: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        out.push(s + i as i32);
    }
    out
}

fn distinct_offsets_stride(start: i32, stride: i32, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    // stride must be >= 1 for distinctness.
    let s = stride.max(1);
    // ensure start + (n-1)*s <= hi
    let max_end = hi as i64;
    let min_start = lo as i64;
    let needed_span = (n as i64 - 1) * s as i64;
    let mut st = start as i64;
    if st + needed_span > max_end {
        st = max_end - needed_span;
    }
    if st < min_start {
        st = min_start;
    }
    let mut out: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        out.push((st + i as i64 * s as i64) as i32);
    }
    out
}

fn distinct_offsets_pairs(n: usize) -> Vec<i32> {
    // Generate values such that minimum difference appears multiple times
    // e.g., 0, 1, 100, 101, 200, 201, ...
    let mut out: Vec<i32> = Vec::with_capacity(n);
    let mut i = 0usize;
    let mut base = 0i32;
    while out.len() < n {
        if i % 2 == 0 {
            out.push(base);
        } else {
            out.push(base + 1);
            base += 100;
        }
        i += 1;
    }
    // clamp to range
    for v in out.iter_mut() {
        if *v > 500_000 { *v = 500_000; }
        if *v < -500_000 { *v = -500_000; }
    }
    // Might have duplicates after clamping in extreme case; fix by deduplicating
    use std::collections::HashSet;
    let mut seen: HashSet<i32> = HashSet::new();
    let mut filtered: Vec<i32> = Vec::new();
    for &v in out.iter() {
        if seen.insert(v) {
            filtered.push(v);
        }
    }
    // fill remaining with random-like values
    let mut fill = -500_000i32;
    while filtered.len() < n {
        if !seen.contains(&fill) {
            filtered.push(fill);
            seen.insert(fill);
        }
        fill += 1;
        if fill > 500_000 { break; }
    }
    filtered
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("]}}");
}

fn build_and_emit(base: i32, n: usize, offsets: Vec<i32>) {
    if offsets.len() != n { return; }
    // verify constraints at runtime
    if !(2 <= n && n <= 100_000) { return; }
    if !(-500_000 <= base && base <= 500_000) { return; }
    for &v in offsets.iter() {
        if !(-500_000 <= v && v <= 500_000) { return; }
    }
    // check distinctness
    {
        use std::collections::HashSet;
        let mut s: HashSet<i32> = HashSet::new();
        for &v in offsets.iter() {
            if !s.insert(v) { return; }
        }
    }
    let arr = generate_test_case(base, n, &offsets);
    print_json(&arr);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let n: usize = match mode {
            0 => 2,
            1 => 3 + (t % 10),
            2 => 100,
            3 => 1000,
            4 => 10_000,
            5 => 2 + (t % 5),
            6 => 50,
            7 => 500,
            8 => 5000,
            _ => 20 + (t % 50),
        };
        // base
        let base = rng.gen_range_i32(-100_000, 100_000);

        let offsets: Vec<i32> = match mode {
            0 => {
                // minimal n=2: two arbitrary distinct offsets
                let a = rng.gen_range_i32(-500_000, 499_999);
                let b = a + 1;
                vec![a, b]
            }
            1 => {
                // consecutive integers
                let start = rng.gen_range_i32(-500_000, 500_000 - n as i32);
                distinct_offsets_consecutive(start, n, -500_000, 500_000)
            }
            2 => {
                // stride random
                let st = rng.gen_range_i32(1, 100);
                let start = rng.gen_range_i32(-400_000, 0);
                distinct_offsets_stride(start, st, n, -500_000, 500_000)
            }
            3 => {
                // large stride
                let st = rng.gen_range_i32(1, 500);
                let start = rng.gen_range_i32(-400_000, -100_000);
                distinct_offsets_stride(start, st, n, -500_000, 500_000)
            }
            4 => {
                // full random
                distinct_offsets_random(&mut rng, n, -500_000, 500_000)
            }
            5 => {
                // tiny n, extreme values
                let mut v: Vec<i32> = Vec::new();
                v.push(-500_000);
                v.push(500_000);
                let mut extra = -499_999i32;
                while v.len() < n {
                    v.push(extra);
                    extra += 1;
                }
                v
            }
            6 => {
                // pair duplicates of minimum diff
                distinct_offsets_pairs(n)
            }
            7 => {
                // negative heavy
                distinct_offsets_random(&mut rng, n, -500_000, -100_000)
            }
            8 => {
                // positive heavy
                distinct_offsets_random(&mut rng, n, 100_000, 500_000)
            }
            _ => {
                // mixed
                distinct_offsets_random(&mut rng, n, -500_000, 500_000)
            }
        };

        let actual_n = offsets.len();
        if actual_n >= 2 {
            build_and_emit(base, actual_n, offsets);
        }
    }
}