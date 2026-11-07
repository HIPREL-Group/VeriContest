use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    na: usize,
    nb: usize,
    a_starts: &Vec<i32>,
    a_ends: &Vec<i32>,
    b_starts: &Vec<i32>,
    b_ends: &Vec<i32>,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        na <= 1000,
        nb <= 1000,
        na + nb >= 1,
        a_starts.len() == na,
        a_ends.len() == na,
        b_starts.len() == nb,
        b_ends.len() == nb,
        forall |i: int| 0 <= i < na as int ==>
            0 <= #[trigger] a_starts[i] && a_starts[i] < a_ends[i] && a_ends[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < na as int - 1 ==>
            #[trigger] a_ends[i] < a_starts[i + 1],
        forall |i: int| 0 <= i < nb as int ==>
            0 <= #[trigger] b_starts[i] && b_starts[i] < b_ends[i] && b_ends[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < nb as int - 1 ==>
            #[trigger] b_ends[i] < b_starts[i + 1],
    ensures
        ({
            let (first, second) = result;
            &&& 0 <= first.len() <= 1000
            &&& 0 <= second.len() <= 1000
            &&& first.len() + second.len() >= 1
            &&& first.len() == na
            &&& second.len() == nb
            &&& (forall |i: int| 0 <= i < first.len() ==> #[trigger] first@[i].len() == 2)
            &&& (forall |i: int| 0 <= i < second.len() ==> #[trigger] second@[i].len() == 2)
            &&& (forall |i: int| 0 <= i < first.len() ==>
                    0 <= (#[trigger] first@[i])[0] && first@[i][0] < first@[i][1] && first@[i][1] <= 1_000_000_000)
            &&& (forall |i: int| 0 <= i < first.len() as int - 1 ==>
                    (#[trigger] first@[i])[1] < first@[i + 1][0])
            &&& (forall |i: int| 0 <= i < second.len() ==>
                    0 <= (#[trigger] second@[i])[0] && second@[i][0] < second@[i][1] && second@[i][1] <= 1_000_000_000)
            &&& (forall |i: int| 0 <= i < second.len() as int - 1 ==>
                    (#[trigger] second@[i])[1] < second@[i + 1][0])
        }),
{
    let mut first: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < na
        invariant
            i <= na,
            first.len() == i,
            a_starts.len() == na,
            a_ends.len() == na,
            forall |k: int| 0 <= k < na as int ==>
                0 <= #[trigger] a_starts[k] && a_starts[k] < a_ends[k] && a_ends[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < na as int - 1 ==>
                #[trigger] a_ends[k] < a_starts[k + 1],
            forall |k: int| 0 <= k < i as int ==> (#[trigger] first@[k]).len() == 2,
            forall |k: int| 0 <= k < i as int ==>
                (#[trigger] first@[k])[0] == a_starts[k] && first@[k][1] == a_ends[k],
        decreases na - i,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(a_starts[i]);
        pair.push(a_ends[i]);
        assert(pair@[0] == a_starts[i as int]);
        assert(pair@[1] == a_ends[i as int]);
        first.push(pair);
        i = i + 1;
    }

    let mut second: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < nb
        invariant
            j <= nb,
            second.len() == j,
            b_starts.len() == nb,
            b_ends.len() == nb,
            forall |k: int| 0 <= k < nb as int ==>
                0 <= #[trigger] b_starts[k] && b_starts[k] < b_ends[k] && b_ends[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < nb as int - 1 ==>
                #[trigger] b_ends[k] < b_starts[k + 1],
            forall |k: int| 0 <= k < j as int ==> (#[trigger] second@[k]).len() == 2,
            forall |k: int| 0 <= k < j as int ==>
                (#[trigger] second@[k])[0] == b_starts[k] && second@[k][1] == b_ends[k],
        decreases nb - j,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(b_starts[j]);
        pair.push(b_ends[j]);
        second.push(pair);
        j = j + 1;
    }

    (first, second)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi { return lo; }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        if lo >= hi { return lo; }
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

// Build a sorted-disjoint list of `n` intervals with:
//  - each interval has length >=1
//  - gap between consecutive intervals >=1
//  - start >= 0, end <= 1_000_000_000
fn make_intervals(rng: &mut Rng, n: usize, max_end: i32, min_len: i32, max_len: i32, min_gap: i32, max_gap: i32) -> (Vec<i32>, Vec<i32>) {
    let mut starts: Vec<i32> = Vec::new();
    let mut ends: Vec<i32> = Vec::new();
    if n == 0 {
        return (starts, ends);
    }
    // budget: total slots needed at least n*(min_len+1) - 1
    // but we ensure end <= max_end
    let mut cur: i32 = 0;
    for i in 0..n {
        // remaining intervals after this: n - 1 - i
        let remaining = (n - 1 - i) as i64;
        // need to leave room: for each remaining: min_gap + min_len
        let reserve = remaining * (min_gap as i64 + min_len as i64);
        let max_start = (max_end as i64 - min_len as i64 - reserve).max(cur as i64);
        let start_pick_hi = max_start.min(cur as i64 + max_gap as i64).max(cur as i64);
        let s = if start_pick_hi > cur as i64 {
            rng.gen_range_i32(cur, start_pick_hi as i32)
        } else {
            cur
        };
        let max_e = (max_end as i64 - reserve).min(s as i64 + max_len as i64);
        let min_e = s as i64 + min_len as i64;
        let e = if max_e > min_e {
            rng.gen_range_i32(min_e as i32, max_e as i32)
        } else {
            min_e as i32
        };
        starts.push(s);
        ends.push(e);
        cur = e + min_gap;
        if cur > max_end - min_len {
            // won't fit more, but loop will end anyway if we're careful
            // if not enough room, break early by changing n - but we promised n
            // So guard: only continues if we reserved correctly
        }
    }
    (starts, ends)
}

// Adversarial: identical intervals on both sides
fn make_identical(n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut s = Vec::new();
    let mut e = Vec::new();
    let mut cur = 0i32;
    for _ in 0..n {
        s.push(cur);
        e.push(cur + 2);
        cur += 4;
    }
    (s, e)
}

// Adversarial: offset by 1
fn make_offset(n: usize, off: i32) -> (Vec<i32>, Vec<i32>) {
    let mut s = Vec::new();
    let mut e = Vec::new();
    let mut cur = off.max(0);
    for _ in 0..n {
        s.push(cur);
        e.push(cur + 2);
        cur += 4;
    }
    (s, e)
}

// Adversarial: one big interval vs many small
fn make_big_small(big_span: i32, small_count: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut a_s = Vec::new();
    let mut a_e = Vec::new();
    a_s.push(0);
    a_e.push(big_span);
    let mut b_s = Vec::new();
    let mut b_e = Vec::new();
    let mut cur = 0i32;
    let step = (big_span / (small_count.max(1) as i32 * 2)).max(2);
    for _ in 0..small_count {
        if cur + step > big_span + 100 { break; }
        b_s.push(cur);
        b_e.push(cur + step / 2);
        cur += step;
    }
    (a_s, a_e, b_s, b_e)
}

fn print_list(name: &str, starts: &[i32], ends: &[i32], first: bool) {
    if !first { print!(","); }
    print!("\"{}\":[", name);
    for i in 0..starts.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", starts[i], ends[i]);
    }
    print!("]");
}

fn print_json(a_s: &[i32], a_e: &[i32], b_s: &[i32], b_e: &[i32]) {
    print!("{{");
    print_list("first_list", a_s, a_e, true);
    print_list("second_list", b_s, b_e, false);
    println!("}}");
}

fn emit(na: usize, a_s: Vec<i32>, a_e: Vec<i32>, nb: usize, b_s: Vec<i32>, b_e: Vec<i32>) {
    // Validate constraints; if violated, skip
    if a_s.len() != na || a_e.len() != na { return; }
    if b_s.len() != nb || b_e.len() != nb { return; }
    if na + nb == 0 { return; }
    for i in 0..na {
        if !(a_s[i] >= 0 && a_s[i] < a_e[i] && a_e[i] <= 1_000_000_000) { return; }
        if i + 1 < na {
            if !(a_e[i] < a_s[i+1]) { return; }
        }
    }
    for i in 0..nb {
        if !(b_s[i] >= 0 && b_s[i] < b_e[i] && b_e[i] <= 1_000_000_000) { return; }
        if i + 1 < nb {
            if !(b_e[i] < b_s[i+1]) { return; }
        }
    }
    let (first, second) = generate_test_case(na, nb, &a_s, &a_e, &b_s, &b_e);
    // Extract to print
    let mut fs: Vec<i32> = Vec::new();
    let mut fe: Vec<i32> = Vec::new();
    for p in &first {
        fs.push(p[0]);
        fe.push(p[1]);
    }
    let mut ss: Vec<i32> = Vec::new();
    let mut se: Vec<i32> = Vec::new();
    for p in &second {
        ss.push(p[0]);
        se.push(p[1]);
    }
    print_json(&fs, &fe, &ss, &se);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);

    let total = 220;
    for t in 0..total {
        let mode = t % 11;
        match mode {
            0 => {
                // small random
                let na = rng.gen_range_usize(0, 6);
                let nb = rng.gen_range_usize(0, 6);
                let na = if na + nb == 0 { 1 } else { na };
                let (a_s, a_e) = make_intervals(&mut rng, na, 200, 1, 10, 1, 10);
                let (b_s, b_e) = make_intervals(&mut rng, nb, 200, 1, 10, 1, 10);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            1 => {
                // empty second
                let na = rng.gen_range_usize(1, 20);
                let (a_s, a_e) = make_intervals(&mut rng, na, 1_000_000, 1, 100, 1, 100);
                emit(a_s.len(), a_s, a_e, 0, Vec::new(), Vec::new());
            }
            2 => {
                // empty first
                let nb = rng.gen_range_usize(1, 20);
                let (b_s, b_e) = make_intervals(&mut rng, nb, 1_000_000, 1, 100, 1, 100);
                emit(0, Vec::new(), Vec::new(), b_s.len(), b_s, b_e);
            }
            3 => {
                // identical
                let n = rng.gen_range_usize(1, 50);
                let (a_s, a_e) = make_identical(n);
                let (b_s, b_e) = make_identical(n);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            4 => {
                // offset
                let n = rng.gen_range_usize(1, 50);
                let (a_s, a_e) = make_identical(n);
                let (b_s, b_e) = make_offset(n, 1);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            5 => {
                // big + small
                let small_count = rng.gen_range_usize(1, 30);
                let (a_s, a_e, b_s, b_e) = make_big_small(1000, small_count);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            6 => {
                // large lists
                let na = rng.gen_range_usize(100, 500);
                let nb = rng.gen_range_usize(100, 500);
                let (a_s, a_e) = make_intervals(&mut rng, na, 1_000_000_000, 1, 100, 1, 100);
                let (b_s, b_e) = make_intervals(&mut rng, nb, 1_000_000_000, 1, 100, 1, 100);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            7 => {
                // max size 1000
                let (a_s, a_e) = make_intervals(&mut rng, 1000, 1_000_000_000, 1, 100, 1, 100);
                let (b_s, b_e) = make_intervals(&mut rng, 1000, 1_000_000_000, 1, 100, 1, 100);
                emit(a_s.len(), a_s, a_e, b_s.len(), b_s, b_e);
            }
            8 => {
                // edge: interval at 0 and 1_000_000_000
                let a_s = vec![0, 999_999_998];
                let a_e = vec![500_000_000, 1_000_000_000];
                let b_s = vec![1, 999_999_999];
                let b_e = vec![500_000_001, 1_000_000_000];
                emit(2, a_s, a_e, 2, b_s, b_e);
            }
            9 => {
                // touching intervals (no overlap)
                // a = [0,5], b = [5,10] -> intersection [5,5]
                let a_s = vec![0, 10, 20];
                let a_e = vec![5, 15, 25];
                let b_s = vec![5, 15, 25];
                let b_e = vec![9, 19, 29];
                emit(3, a_s, a_e, 3, b_s, b_e);
            }
            _ => {
                // single element each
                let a = rng.gen_range_i32(0, 999_999_990);
                let a_s = vec![a];
                let a_e = vec![a + 5];
                let b = rng.gen_range_i32(0, 999_999_990);
                let b_s = vec![b];
                let b_e = vec![b + 5];
                emit(1, a_s, a_e, 1, b_s, b_e);
            }
        }
    }
}