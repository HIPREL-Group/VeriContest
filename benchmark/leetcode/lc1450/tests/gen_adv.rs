use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: &Vec<i32>,
    offsets: &Vec<i32>,
    query_time: i32,
) -> (res: (Vec<i32>, Vec<i32>, i32))
    requires
        starts.len() == offsets.len(),
        1 <= starts.len() <= 100,
        1 <= query_time <= 1000,
        forall |i: int| 0 <= i < starts.len() ==>
            1 <= #[trigger] starts[i] <= 1000,
        forall |i: int| 0 <= i < offsets.len() ==>
            0 <= #[trigger] offsets[i] && (offsets[i] as int + starts[i] as int) <= 1000,
    ensures
        res.0.len() == res.1.len(),
        1 <= res.0.len() <= 100,
        forall |i: int| 0 <= i < res.0.len() ==>
            1 <= #[trigger] res.0[i] <= res.1[i] <= 1000,
        1 <= res.2 <= 1000,
        res.2 == query_time,
{
    let n = starts.len();
    let mut start_time: Vec<i32> = Vec::new();
    let mut end_time: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == starts.len(),
            n == offsets.len(),
            0 <= i <= n,
            start_time.len() == i,
            end_time.len() == i,
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] start_time[k] == starts[k],
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] end_time[k] as int == starts[k] as int + offsets[k] as int,
            forall |k: int| 0 <= k < starts.len() ==>
                1 <= #[trigger] starts[k] <= 1000,
            forall |k: int| 0 <= k < offsets.len() ==>
                0 <= #[trigger] offsets[k] && (offsets[k] as int + starts[k] as int) <= 1000,
        decreases n - i,
    {
        let s = starts[i];
        let o = offsets[i];
        let e: i32 = s + o;
        start_time.push(s);
        end_time.push(e);
        i = i + 1;
    }

    assert(start_time.len() == n);
    assert(end_time.len() == n);

    assert forall |k: int| 0 <= k < start_time.len() implies
        1 <= #[trigger] start_time[k] <= end_time[k] <= 1000
    by {
        assert(start_time[k] == starts[k]);
        assert(end_time[k] as int == starts[k] as int + offsets[k] as int);
        assert(1 <= starts[k] <= 1000);
        assert(0 <= offsets[k]);
        assert(offsets[k] as int + starts[k] as int <= 1000);
    }

    (start_time, end_time, query_time)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>, i32) {
    let n: usize;
    let query_time: i32;
    let mut starts: Vec<i32> = Vec::new();
    let mut offsets: Vec<i32> = Vec::new();

    match mode {
        0 => {
            // minimal n=1
            n = 1;
            query_time = rng.gen_range_i32(1, 1000);
            starts.push(rng.gen_range_i32(1, 1000));
            let s = starts[0];
            offsets.push(rng.gen_range_i32(0, 1000 - s));
        }
        1 => {
            // max n=100
            n = 100;
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 1000);
                starts.push(s);
                offsets.push(rng.gen_range_i32(0, 1000 - s));
            }
        }
        2 => {
            // all intervals cover queryTime
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, query_time);
                starts.push(s);
                offsets.push(rng.gen_range_i32(query_time - s, 1000 - s));
            }
        }
        3 => {
            // no intervals cover queryTime
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(2, 999);
            for _ in 0..n {
                // either end before queryTime or start after queryTime
                if rng.next_u64() % 2 == 0 && query_time >= 2 {
                    let s = rng.gen_range_i32(1, query_time - 1);
                    let max_e = query_time - 1;
                    let off = rng.gen_range_i32(0, max_e - s);
                    starts.push(s);
                    offsets.push(off);
                } else {
                    let s = rng.gen_range_i32(query_time + 1, 1000);
                    starts.push(s);
                    offsets.push(rng.gen_range_i32(0, 1000 - s));
                }
            }
        }
        4 => {
            // queryTime = 1
            n = rng.gen_range_usize(1, 100);
            query_time = 1;
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 1000);
                starts.push(s);
                offsets.push(rng.gen_range_i32(0, 1000 - s));
            }
        }
        5 => {
            // queryTime = 1000
            n = rng.gen_range_usize(1, 100);
            query_time = 1000;
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 1000);
                starts.push(s);
                offsets.push(rng.gen_range_i32(0, 1000 - s));
            }
        }
        6 => {
            // boundary cases: start==query or end==query
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                let choice = rng.next_u64() % 3;
                if choice == 0 {
                    // start == queryTime
                    let s = query_time;
                    starts.push(s);
                    offsets.push(rng.gen_range_i32(0, 1000 - s));
                } else if choice == 1 && query_time >= 1 {
                    // end == queryTime
                    let s = rng.gen_range_i32(1, query_time);
                    starts.push(s);
                    offsets.push(query_time - s);
                } else {
                    let s = rng.gen_range_i32(1, 1000);
                    starts.push(s);
                    offsets.push(rng.gen_range_i32(0, 1000 - s));
                }
            }
        }
        7 => {
            // all zero-length intervals (start==end)
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 1000);
                starts.push(s);
                offsets.push(0);
            }
        }
        8 => {
            // all intervals [1,1000]
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                starts.push(1);
                offsets.push(999);
            }
        }
        _ => {
            // random
            n = rng.gen_range_usize(1, 100);
            query_time = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 1000);
                starts.push(s);
                offsets.push(rng.gen_range_i32(0, 1000 - s));
            }
        }
    }

    generate_test_case(&starts, &offsets, query_time)
}

fn print_json(start_time: &[i32], end_time: &[i32], query_time: i32) {
    print!("{{\"start_time\":[");
    for i in 0..start_time.len() {
        if i > 0 { print!(","); }
        print!("{}", start_time[i]);
    }
    print!("],\"end_time\":[");
    for i in 0..end_time.len() {
        if i > 0 { print!(","); }
        print!("{}", end_time[i]);
    }
    println!("],\"query_time\":{}}}", query_time);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (s, e, q) = build_case(&mut rng, mode);
        print_json(&s, &e, q);
    }
}