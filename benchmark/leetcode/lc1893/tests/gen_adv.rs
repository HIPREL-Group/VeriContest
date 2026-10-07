use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    starts: &Vec<i32>,
    ends: &Vec<i32>,
    left: i32,
    right: i32,
) -> (result: (Vec<Vec<i32>>, i32, i32))
    requires
        1 <= n <= 50,
        starts.len() == n,
        ends.len() == n,
        1 <= left <= right <= 50,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] starts[i] && starts[i] <= ends[i] && ends[i] <= 50,
    ensures
        ({
            let ranges = result.0;
            let l = result.1;
            let r = result.2;
            &&& 1 <= ranges.len() <= 50
            &&& 1 <= l <= r <= 50
            &&& l == left
            &&& r == right
            &&& forall|j: int| 0 <= j < ranges.len() ==> #[trigger] ranges[j]@.len() == 2
            &&& forall|j: int| 0 <= j < ranges.len() ==> 1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50
        }),
{
    let mut ranges: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 50,
            starts.len() == n,
            ends.len() == n,
            ranges.len() == i,
            forall|k: int| 0 <= k < n ==> 1 <= #[trigger] starts[k] && starts[k] <= ends[k] && ends[k] <= 50,
            forall|j: int| 0 <= j < ranges.len() ==> #[trigger] ranges[j]@.len() == 2,
            forall|j: int| 0 <= j < ranges.len() ==> 1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50,
        decreases n - i,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(starts[i]);
        pair.push(ends[i]);
        assert(pair@.len() == 2);
        assert(pair[0] == starts[i as int]);
        assert(pair[1] == ends[i as int]);
        ranges.push(pair);
        i = i + 1;
    }
    (ranges, left, right)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (usize, Vec<i32>, Vec<i32>, i32, i32) {
    let (left, right) = {
        let a = rng.gen_i32(1, 50);
        let b = rng.gen_i32(1, 50);
        if a <= b { (a, b) } else { (b, a) }
    };
    let n: usize;
    let mut starts: Vec<i32> = Vec::new();
    let mut ends: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // Full coverage by one range [1,50]
            n = 1;
            starts.push(1);
            ends.push(50);
        }
        1 => {
            // Fully covers [left,right] exactly
            n = 1;
            starts.push(left);
            ends.push(right);
        }
        2 => {
            // Misses one value inside [left,right]
            n = 2;
            if left < right {
                starts.push(left);
                ends.push(left);
                starts.push(right);
                ends.push(right);
            } else {
                starts.push(1);
                ends.push(1);
                starts.push(50);
                ends.push(50);
            }
        }
        3 => {
            // ranges all below left
            n = rng.gen_usize(1, 5);
            for _ in 0..n {
                let hi = if left > 1 { left - 1 } else { 1 };
                let s = rng.gen_i32(1, hi);
                let e = rng.gen_i32(s, hi);
                starts.push(s);
                ends.push(e);
            }
        }
        4 => {
            // ranges all above right
            n = rng.gen_usize(1, 5);
            for _ in 0..n {
                let lo = if right < 50 { right + 1 } else { 50 };
                let s = rng.gen_i32(lo, 50);
                let e = rng.gen_i32(s, 50);
                starts.push(s);
                ends.push(e);
            }
        }
        5 => {
            // Many small unit ranges covering [left,right]
            let mut v = Vec::new();
            for x in left..=right {
                v.push(x);
            }
            n = v.len();
            for x in v {
                starts.push(x);
                ends.push(x);
            }
        }
        6 => {
            // Single point range
            n = 1;
            let p = rng.gen_i32(1, 50);
            starts.push(p);
            ends.push(p);
        }
        7 => {
            // Maximum 50 ranges random
            n = 50;
            for _ in 0..n {
                let s = rng.gen_i32(1, 50);
                let e = rng.gen_i32(s, 50);
                starts.push(s);
                ends.push(e);
            }
        }
        8 => {
            // Overlapping ranges covering [left,right] with gap off-by-one
            n = 2;
            let mid = (left + right) / 2;
            starts.push(left);
            ends.push(mid);
            starts.push(mid + 1);
            ends.push(right);
            if mid + 1 > 50 {
                // adjust
                starts.clear();
                ends.clear();
                starts.push(1);
                ends.push(50);
            }
        }
        9 => {
            // left == right boundary cases
            n = rng.gen_usize(1, 5);
            for _ in 0..n {
                let s = rng.gen_i32(1, 50);
                let e = rng.gen_i32(s, 50);
                starts.push(s);
                ends.push(e);
            }
        }
        _ => {
            n = rng.gen_usize(1, 50);
            for _ in 0..n {
                let s = rng.gen_i32(1, 50);
                let e = rng.gen_i32(s, 50);
                starts.push(s);
                ends.push(e);
            }
        }
    }
    // Sanity: ensure starts.len() == n and all valid
    if starts.len() != n || ends.len() != n {
        // fallback
        let mut s2 = Vec::new();
        let mut e2 = Vec::new();
        s2.push(1i32);
        e2.push(50i32);
        return (1, s2, e2, left, right);
    }
    for i in 0..n {
        if !(starts[i] >= 1 && starts[i] <= ends[i] && ends[i] <= 50) {
            let mut s2 = Vec::new();
            let mut e2 = Vec::new();
            s2.push(1i32);
            e2.push(50i32);
            return (1, s2, e2, left, right);
        }
    }
    (n, starts, ends, left, right)
}

fn print_json(ranges: &Vec<Vec<i32>>, left: i32, right: i32) {
    print!("{{\"ranges\":[");
    for i in 0..ranges.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", ranges[i][0], ranges[i][1]);
    }
    println!("],\"left\":{},\"right\":{}}}", left, right);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (n, starts, ends, left, right) = build_case(&mut rng, mode);
        let (ranges, l, r) = generate_test_case(n, &starts, &ends, left, right);
        print_json(&ranges, l, r);
    }
}