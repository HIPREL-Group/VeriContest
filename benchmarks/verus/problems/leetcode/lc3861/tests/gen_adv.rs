use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    cap: &Vec<i32>,
    item_size: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= cap.len() <= 100,
        forall |k: int| 0 <= k < cap.len() ==> 1 <= #[trigger] cap[k] <= 100,
        1 <= item_size <= 100,
    ensures
        1 <= res.0.len() <= 100,
        forall |k: int| 0 <= k < res.0.len() ==> 1 <= #[trigger] res.0[k] <= 100,
        1 <= res.1 <= 100,
{
    let n = cap.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == cap.len(),
            0 <= i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < cap.len() ==> 1 <= #[trigger] cap[k] <= 100,
            forall |k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 100,
            forall |k: int| 0 <= k < out.len() ==> out[k] == cap[k],
        decreases n - i,
    {
        let v = cap[i];
        assert(1 <= v <= 100);
        out.push(v);
        i = i + 1;
    }
    (out, item_size)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // tiny, single element, item fits
            let v = rng.gen_range_i32(1, 100);
            let item = rng.gen_range_i32(1, v);
            (vec![v], item)
        }
        1 => {
            // tiny, single element, item does NOT fit
            let v = rng.gen_range_i32(1, 99);
            let item = rng.gen_range_i32(v + 1, 100);
            (vec![v], item)
        }
        2 => {
            // all elements less than item -> -1
            let n = rng.gen_range_usize(1, 100);
            let item: i32 = 100;
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                c.push(rng.gen_range_i32(1, 99));
            }
            (c, item)
        }
        3 => {
            // all equal capacity
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(1, 100);
            let item = rng.gen_range_i32(1, 100);
            let c = vec![v; n];
            (c, item)
        }
        4 => {
            // duplicates of the minimum valid value (test smallest-index tiebreak)
            let n = rng.gen_range_usize(2, 100);
            let item = rng.gen_range_i32(1, 50);
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                // mix of valid (=item) and lower
                if rng.next_u64() % 2 == 0 {
                    c.push(item);
                } else {
                    c.push(rng.gen_range_i32(1, item));
                }
            }
            (c, item)
        }
        5 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 100);
            let mut c = Vec::with_capacity(n);
            let mut cur: i32 = 1;
            for _ in 0..n {
                c.push(cur);
                if cur < 100 {
                    cur += 1;
                }
            }
            let item = rng.gen_range_i32(1, 100);
            (c, item)
        }
        6 => {
            // sorted descending
            let n = rng.gen_range_usize(1, 100);
            let mut c = Vec::with_capacity(n);
            let mut cur: i32 = 100;
            for _ in 0..n {
                c.push(cur);
                if cur > 1 {
                    cur -= 1;
                }
            }
            let item = rng.gen_range_i32(1, 100);
            (c, item)
        }
        7 => {
            // boundary - item_size = 1, always all valid
            let n = rng.gen_range_usize(1, 100);
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                c.push(rng.gen_range_i32(1, 100));
            }
            (c, 1)
        }
        8 => {
            // boundary - item_size = 100
            let n = rng.gen_range_usize(1, 100);
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                c.push(rng.gen_range_i32(1, 100));
            }
            (c, 100)
        }
        9 => {
            // max size with random
            let n = 100;
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                c.push(rng.gen_range_i32(1, 100));
            }
            let item = rng.gen_range_i32(1, 100);
            (c, item)
        }
        _ => {
            // general random
            let n = rng.gen_range_usize(1, 100);
            let mut c = Vec::with_capacity(n);
            for _ in 0..n {
                c.push(rng.gen_range_i32(1, 100));
            }
            let item = rng.gen_range_i32(1, 100);
            (c, item)
        }
    }
}

fn print_json(cap: &[i32], item_size: i32) {
    print!("{{\"capacity\":[");
    for i in 0..cap.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", cap[i]);
    }
    println!("],\"item_size\":{}}}", item_size);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (cap_vec, item_size) = build_case(mode, &mut rng);
        let (out_cap, out_item) = generate_test_case(&cap_vec, item_size);
        print_json(&out_cap, out_item);
    }
}