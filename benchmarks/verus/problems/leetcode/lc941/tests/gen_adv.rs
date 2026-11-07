use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= fillers.len() <= 10_000,
        forall |k: int| 0 <= k < fillers.len() ==> 0 <= #[trigger] fillers[k] <= 10_000,
    ensures
        1 <= arr.len() <= 10_000,
        forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
{
    let mut arr: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 0 <= #[trigger] fillers[k] <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
        decreases n - i,
    {
        arr.push(fillers[i]);
        i = i + 1;
    }
    arr
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_valid_mountain(rng: &mut Rng, n: usize) -> Vec<i32> {
    // n >= 3
    let peak = rng.gen_range_usize(1, n - 2);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let mut cur: i32 = rng.gen_range_i32(0, 100);
    v.push(cur);
    for _ in 1..=peak {
        let inc = rng.gen_range_i32(1, 50);
        cur = (cur + inc).min(10_000);
        if cur == *v.last().unwrap() {
            cur = (cur + 1).min(10_000);
        }
        v.push(cur);
    }
    // ensure strictly ascending; fix if clamped
    for i in 1..=peak {
        if v[i] <= v[i-1] {
            v[i] = (v[i-1] + 1).min(10_000);
        }
    }
    // descending
    for _ in (peak+1)..n {
        let dec = rng.gen_range_i32(1, 50);
        cur = (cur - dec).max(0);
        v.push(cur);
    }
    for i in (peak+1)..n {
        if v[i] >= v[i-1] {
            v[i] = (v[i-1] - 1).max(0);
        }
    }
    // if constraints still violated, rebuild deterministically
    let mut ok = v.len() == n;
    for i in 1..=peak { if v[i] <= v[i-1] { ok = false; } }
    for i in (peak+1)..n { if v[i] >= v[i-1] { ok = false; } }
    for i in 0..n { if v[i] < 0 || v[i] > 10_000 { ok = false; } }
    if !ok {
        v.clear();
        // build triangle: 0..peak, then peak-1..0
        for i in 0..=peak { v.push(i as i32); }
        for i in 0..(n - peak - 1) {
            v.push((peak as i32) - 1 - i as i32);
        }
        // adjust if goes negative
        let mut min_v = 0i32;
        for &x in &v { if x < min_v { min_v = x; } }
        if min_v < 0 {
            for x in &mut v { *x -= min_v; }
        }
        // clamp
        for x in &mut v {
            if *x < 0 { *x = 0; }
            if *x > 10_000 { *x = 10_000; }
        }
    }
    v
}

fn make_invalid_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(0, 10_000));
    }
    v
}

fn adversarial(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    match mode {
        0 => {
            // strictly increasing (no descending)
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push((i as i32).min(10_000)); }
            v
        }
        1 => {
            // strictly decreasing (no ascending)
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(((n - 1 - i) as i32).min(10_000)); }
            v
        }
        2 => {
            // all equal
            let c = rng.gen_range_i32(0, 10_000);
            vec![c; n]
        }
        3 => {
            // plateau at peak
            let peak = n / 2;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i <= peak { v.push(i as i32); }
                else if i == peak + 1 { v.push(peak as i32); } // equal
                else { v.push((peak as i32) - (i as i32 - peak as i32 - 1)); }
            }
            for x in &mut v {
                if *x < 0 { *x = 0; }
                if *x > 10_000 { *x = 10_000; }
            }
            v
        }
        4 => {
            // peak at 0 (no left side)
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(((n - i) as i32).min(10_000)); }
            v
        }
        5 => {
            // peak at end (no right side)
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push((i as i32).min(10_000)); }
            v
        }
        6 => {
            // length < 3: n=1 or 2
            let actual_n = if n > 2 { 2 } else { n };
            let mut v = Vec::with_capacity(actual_n);
            for i in 0..actual_n { v.push(i as i32); }
            v
        }
        7 => make_valid_mountain(rng, n.max(3)),
        8 => {
            // two peaks
            let mut v = Vec::with_capacity(n);
            let quarter = n / 4;
            for i in 0..n {
                let vv = if i <= quarter { i as i32 }
                         else if i <= 2*quarter { (2*quarter - i) as i32 }
                         else if i <= 3*quarter { (i - 2*quarter) as i32 }
                         else { (n - i) as i32 };
                v.push(vv.max(0).min(10_000));
            }
            v
        }
        9 => make_invalid_random(rng, n),
        _ => make_valid_mountain(rng, n.max(3)),
    }
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            6 => if t % 2 == 0 { 1 } else { 2 },
            0 | 1 => rng.gen_range_usize(3, 20),
            2 => rng.gen_range_usize(3, 10),
            3 => rng.gen_range_usize(5, 30),
            4 | 5 => rng.gen_range_usize(3, 15),
            7 => rng.gen_range_usize(3, 100),
            8 => rng.gen_range_usize(8, 50),
            9 => rng.gen_range_usize(3, 50),
            _ => rng.gen_range_usize(3, 10_000),
        };
        let raw = adversarial(&mut rng, mode, n);
        // clamp to valid ranges and lengths
        let mut fillers: Vec<i32> = raw.into_iter()
            .map(|x| if x < 0 { 0 } else if x > 10_000 { 10_000 } else { x })
            .collect();
        if fillers.is_empty() { fillers.push(0); }
        if fillers.len() > 10_000 { fillers.truncate(10_000); }
        let arr = generate_test_case(&fillers);
        print_json(&arr);
    }
}