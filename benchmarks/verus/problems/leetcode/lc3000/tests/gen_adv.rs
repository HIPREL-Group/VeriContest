use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: &Vec<(i32, i32)>) -> (result: Vec<Vec<i32>>)
    requires
        1 <= raw.len() <= 100,
        forall |i: int| 0 <= i < raw.len() ==> 1 <= (#[trigger] raw[i]).0 <= 100,
        forall |i: int| 0 <= i < raw.len() ==> 1 <= (#[trigger] raw[i]).1 <= 100,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]).len() == 2,
        forall |i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 100,
        forall |i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[1] <= 100,
{
    let n = raw.len();
    let mut out: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw.len(),
            1 <= n <= 100,
            0 <= i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < raw.len() ==> 1 <= (#[trigger] raw[k]).0 <= 100,
            forall |k: int| 0 <= k < raw.len() ==> 1 <= (#[trigger] raw[k]).1 <= 100,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] out[k]).len() == 2,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] out[k])[0] == raw[k].0,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] out[k])[1] == raw[k].1,
        decreases n - i,
    {
        let p = raw[i];
        let mut inner: Vec<i32> = Vec::new();
        inner.push(p.0);
        inner.push(p.1);
        assert(inner.len() == 2);
        assert(inner[0] == p.0);
        assert(inner[1] == p.1);
        out.push(inner);
        assert(out[i as int].len() == 2);
        assert(out[i as int][0] == raw[i as int].0);
        assert(out[i as int][1] == raw[i as int].1);
        i = i + 1;
    }

    proof {
        assert forall |k: int| 0 <= k < out.len() implies 1 <= (#[trigger] out[k])[0] <= 100 by {
            assert(out[k][0] == raw[k].0);
            assert(1 <= raw[k].0 <= 100);
        }
        assert forall |k: int| 0 <= k < out.len() implies 1 <= (#[trigger] out[k])[1] <= 100 by {
            assert(out[k][1] == raw[k].1);
            assert(1 <= raw[k].1 <= 100);
        }
        assert forall |k: int| 0 <= k < out.len() implies (#[trigger] out[k]).len() == 2 by {
        }
    }

    out
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

fn build_mode(rng: &mut Rng, mode: usize, idx: usize) -> Vec<(i32, i32)> {
    let mut v: Vec<(i32, i32)> = Vec::new();
    match mode {
        0 => {
            // Single element
            let l = rng.gen_range_i32(1, 100);
            let w = rng.gen_range_i32(1, 100);
            v.push((l, w));
        }
        1 => {
            // All same diagonal, different areas
            // e.g. (3,4) and (4,3) -- same diag 25, area 12
            let n = rng.gen_range_usize(2, 10);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push((3, 4));
                } else {
                    v.push((4, 3));
                }
            }
        }
        2 => {
            // Increasing diagonals
            let n = rng.gen_range_usize(2, 20);
            for i in 0..n {
                let s = ((i + 1) as i32).min(100).max(1);
                v.push((s, s));
            }
        }
        3 => {
            // Decreasing diagonals
            let n = rng.gen_range_usize(2, 20);
            for i in 0..n {
                let s = (100 - i as i32).max(1);
                v.push((s, s));
            }
        }
        4 => {
            // Maximum size array
            for _ in 0..100 {
                let l = rng.gen_range_i32(1, 100);
                let w = rng.gen_range_i32(1, 100);
                v.push((l, w));
            }
        }
        5 => {
            // All same rectangle
            let l = rng.gen_range_i32(1, 100);
            let w = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                v.push((l, w));
            }
        }
        6 => {
            // Boundary values
            let n = rng.gen_range_usize(1, 10);
            for _ in 0..n {
                let l = if rng.next_u64() % 2 == 0 { 1 } else { 100 };
                let w = if rng.next_u64() % 2 == 0 { 1 } else { 100 };
                v.push((l, w));
            }
        }
        7 => {
            // Last has largest diagonal
            let n = rng.gen_range_usize(2, 20);
            for i in 0..n {
                let s = if i + 1 == n { 100 } else { rng.gen_range_i32(1, 50) };
                v.push((s, s));
            }
        }
        8 => {
            // First has largest diagonal
            let n = rng.gen_range_usize(2, 20);
            for i in 0..n {
                let s = if i == 0 { 100 } else { rng.gen_range_i32(1, 50) };
                v.push((s, s));
            }
        }
        9 => {
            // Two rects with same diagonal but very different areas, at specific positions
            let n = rng.gen_range_usize(2, 10);
            for i in 0..n {
                if i == 0 {
                    v.push((3, 4));
                } else if i == n / 2 {
                    v.push((5, 1));
                } else {
                    v.push((2, 2));
                }
            }
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                let l = rng.gen_range_i32(1, 100);
                let w = rng.gen_range_i32(1, 100);
                v.push((l, w));
            }
        }
    }
    let _ = idx;
    v
}

fn print_json(dims: &[Vec<i32>]) {
    print!("{{\"dimensions\":[");
    for i in 0..dims.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", dims[i][0], dims[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let raw = build_mode(&mut rng, mode, t);
        if raw.is_empty() || raw.len() > 100 {
            continue;
        }
        let mut valid = true;
        for &(a, b) in raw.iter() {
            if a < 1 || a > 100 || b < 1 || b > 100 {
                valid = false;
                break;
            }
        }
        if !valid {
            continue;
        }
        let result = generate_test_case(&raw);
        print_json(&result);
    }
}