use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    h: i32,
    w: i32,
    hcuts: Vec<i32>,
    vcuts: Vec<i32>,
) -> (result: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        2 <= h <= 1_000_000_000,
        2 <= w <= 1_000_000_000,
        1 <= hcuts.len() <= 100_000,
        1 <= vcuts.len() <= 100_000,
        forall |i: int| 0 <= i < hcuts.len() ==> 1 <= #[trigger] hcuts[i] < h,
        forall |j: int| 0 <= j < vcuts.len() ==> 1 <= #[trigger] vcuts[j] < w,
        forall |i: int, j: int| 0 <= i < j < hcuts.len() ==> hcuts[i] != hcuts[j],
        forall |i: int, j: int| 0 <= i < j < vcuts.len() ==> vcuts[i] != vcuts[j],
    ensures
        ({
            let (rh, rw, rhc, rvc) = result;
            &&& 2 <= rh <= 1_000_000_000
            &&& 2 <= rw <= 1_000_000_000
            &&& 1 <= rhc.len() <= 100_000
            &&& 1 <= rvc.len() <= 100_000
            &&& (forall |i: int| 0 <= i < rhc.len() ==> 1 <= #[trigger] rhc[i] < rh)
            &&& (forall |j: int| 0 <= j < rvc.len() ==> 1 <= #[trigger] rvc[j] < rw)
            &&& (forall |i: int, j: int| 0 <= i < j < rhc.len() ==> rhc[i] != rhc[j])
            &&& (forall |i: int, j: int| 0 <= i < j < rvc.len() ==> rvc[i] != rvc[j])
        }),
{
    (h, w, hcuts, vcuts)
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

// Generate `count` distinct integers in [1, bound-1], random or structured.
fn distinct_cuts(rng: &mut Rng, count: usize, bound: i32, mode: usize) -> Vec<i32> {
    // bound >= 2, count <= min(bound-1, 100_000), count >= 1
    let mut result: Vec<i32> = Vec::with_capacity(count);
    let max_val = (bound - 1) as i64;

    match mode {
        0 => {
            // Sequential 1,2,3,...,count
            for i in 0..count {
                result.push((i as i32) + 1);
            }
        }
        1 => {
            // Sequential from the top: bound-1, bound-2, ...
            for i in 0..count {
                result.push((bound - 1) - (i as i32));
            }
        }
        2 => {
            // Evenly spaced
            for i in 0..count {
                let v = 1 + ((i as i64) * max_val / (count as i64).max(1)) as i32;
                let v = v.max(1).min(bound - 1);
                // ensure distinct by linear probing
                let mut vv = v;
                while result.iter().any(|&x| x == vv) {
                    vv += 1;
                    if vv >= bound { vv = 1; }
                }
                result.push(vv);
            }
        }
        _ => {
            // Random distinct
            // Use a boolean trick: try random values; fallback with linear probe.
            let mut i = 0;
            while i < count {
                let v = rng.gen_range_i32(1, bound - 1);
                if !result.iter().any(|&x| x == v) {
                    result.push(v);
                    i += 1;
                } else {
                    // linear probe
                    let mut vv = v;
                    let mut tries = 0;
                    while result.iter().any(|&x| x == vv) && tries < (bound as i64).min(1000) as i32 {
                        vv = if vv >= bound - 1 { 1 } else { vv + 1 };
                        tries += 1;
                    }
                    if !result.iter().any(|&x| x == vv) {
                        result.push(vv);
                        i += 1;
                    }
                }
            }
        }
    }
    result
}

fn print_json(h: i32, w: i32, hc: &[i32], vc: &[i32]) {
    print!("{{\"h\":{},\"w\":{},\"horizontal_cuts\":[", h, w);
    for i in 0..hc.len() {
        if i > 0 { print!(","); }
        print!("{}", hc[i]);
    }
    print!("],\"vertical_cuts\":[");
    for i in 0..vc.len() {
        if i > 0 { print!(","); }
        print!("{}", vc[i]);
    }
    println!("]}}");
}

fn build_and_print(rng: &mut Rng, h: i32, w: i32, hn: usize, vn: usize, mode_h: usize, mode_v: usize) {
    let hc = distinct_cuts(rng, hn, h, mode_h);
    let vc = distinct_cuts(rng, vn, w, mode_v);

    // Verify the preconditions at runtime before calling.
    if hc.len() < 1 || hc.len() > 100_000 { return; }
    if vc.len() < 1 || vc.len() > 100_000 { return; }
    for &x in &hc { if x < 1 || x >= h { return; } }
    for &x in &vc { if x < 1 || x >= w { return; } }
    // distinctness
    let mut hc_sorted = hc.clone();
    hc_sorted.sort();
    for i in 1..hc_sorted.len() { if hc_sorted[i] == hc_sorted[i-1] { return; } }
    let mut vc_sorted = vc.clone();
    vc_sorted.sort();
    for i in 1..vc_sorted.len() { if vc_sorted[i] == vc_sorted[i-1] { return; } }

    let (rh, rw, rhc, rvc) = generate_test_case(h, w, hc, vc);
    print_json(rh, rw, &rhc, &rvc);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200;
    for t in 0..total {
        let mode = t % 14;
        match mode {
            0 => {
                // minimal: h=2,w=2,single cut
                build_and_print(&mut rng, 2, 2, 1, 1, 0, 0);
            }
            1 => {
                // h,w small, cuts sequential
                let h = rng.gen_range_i32(3, 20);
                let w = rng.gen_range_i32(3, 20);
                let hn = rng.gen_range_usize(1, (h as usize) - 1);
                let vn = rng.gen_range_usize(1, (w as usize) - 1);
                build_and_print(&mut rng, h, w, hn, vn, 0, 0);
            }
            2 => {
                // large h,w small cuts
                let h = 1_000_000_000;
                let w = 1_000_000_000;
                build_and_print(&mut rng, h, w, 1, 1, 0, 0);
            }
            3 => {
                // one cut near edge
                let h = rng.gen_range_i32(100, 1_000_000);
                let w = rng.gen_range_i32(100, 1_000_000);
                build_and_print(&mut rng, h, w, 1, 1, 1, 1);
            }
            4 => {
                // many cuts spread
                let h: i32 = 1_000_000_000;
                let w: i32 = 1_000_000_000;
                build_and_print(&mut rng, h, w, 1000, 1000, 2, 2);
            }
            5 => {
                // maximum cuts
                let h: i32 = 100_001;
                let w: i32 = 100_001;
                build_and_print(&mut rng, h, w, 100_000, 100_000, 0, 1);
            }
            6 => {
                // cuts concentrated low
                let h: i32 = 1_000_000_000;
                let w: i32 = 1_000_000_000;
                build_and_print(&mut rng, h, w, 100, 100, 0, 0);
            }
            7 => {
                // cuts concentrated high
                let h: i32 = 1_000_000_000;
                let w: i32 = 1_000_000_000;
                build_and_print(&mut rng, h, w, 100, 100, 1, 1);
            }
            8 => {
                // random medium
                let h = rng.gen_range_i32(100, 100_000);
                let w = rng.gen_range_i32(100, 100_000);
                let hn = rng.gen_range_usize(1, 50);
                let vn = rng.gen_range_usize(1, 50);
                build_and_print(&mut rng, h, w, hn, vn, 3, 3);
            }
            9 => {
                // Asymmetric: tiny h, big w
                let h: i32 = 2;
                let w: i32 = 1_000_000_000;
                build_and_print(&mut rng, h, w, 1, 500, 0, 3);
            }
            10 => {
                // Asymmetric other way
                let h: i32 = 1_000_000_000;
                let w: i32 = 2;
                build_and_print(&mut rng, h, w, 500, 1, 3, 0);
            }
            11 => {
                // Equal cuts pattern
                let h: i32 = 1000;
                let w: i32 = 1000;
                build_and_print(&mut rng, h, w, 999, 999, 0, 0);
            }
            12 => {
                // Single cut in middle
                let h = rng.gen_range_i32(4, 1_000_000);
                let w = rng.gen_range_i32(4, 1_000_000);
                build_and_print(&mut rng, h, w, 1, 1, 3, 3);
            }
            _ => {
                // Completely random
                let h = rng.gen_range_i32(2, 1_000_000_000);
                let w = rng.gen_range_i32(2, 1_000_000_000);
                let hmax = ((h as usize) - 1).min(1000);
                let wmax = ((w as usize) - 1).min(1000);
                let hn = rng.gen_range_usize(1, hmax.max(1));
                let vn = rng.gen_range_usize(1, wmax.max(1));
                build_and_print(&mut rng, h, w, hn, vn, 3, 3);
            }
        }
    }
}