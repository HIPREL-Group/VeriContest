use vstd::prelude::*;

verus! {
pub open spec fn valid_event(e: Seq<i32>) -> bool {
    e.len() == 2 && 1 <= e[0] <= 100000 && 1 <= e[1] <= 100000
}

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> valid_event(#[trigger] result[i]@),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 100000 && 1 <= result[i][1] <= 100000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i][1] < #[trigger] result[j][1],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous = 0i32;
    while i < count
        invariant
            1 <= count <= 1000, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 100000 && 1 <= result[j][1] <= 100000,
            0 <= previous <= 100000 - count as int + i as int,
            i > 0 ==> result[i - 1][1] == previous,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> #[trigger] result[j][1] < #[trigger] result[k][1],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 100000 { 100000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 100000 { 100000 } else { b };
        let upper = 100000 - count as i32 + i as i32 + 1;
        let v = b;
        let v = if v > upper { upper } else { v };
        let v = if v <= previous { previous + 1 } else { v };
        b = v;
        assert forall|j: int| 0 <= j < result.len() implies result[j][1] < v by {
            if j < i - 1 { assert(result[j][1] < result[(i - 1) as int][1]); }
        }
        previous = v;
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    assert forall|j: int| 0 <= j < result.len() implies valid_event(#[trigger] result[j]@) by {
        assert(result[j].len() == 2);
        assert(1 <= result[j][0] <= 100000 && 1 <= result[j][1] <= 100000);
    }
    result
}


pub fn generate_candidate(
    indices: &Vec<i32>,
    times: &Vec<i32>,
) -> (events: Vec<Vec<i32>>)
    requires
        indices.len() == times.len(),
        1 <= indices.len() <= 1000,
        forall|i: int| 0 <= i < indices.len() ==> 1 <= #[trigger] indices[i] <= 100000,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 100000,
        forall|i: int, j: int| 0 <= i < j < times.len() ==> times[i] <= times[j],
    ensures
        1 <= events.len() <= 1000,
        forall|i: int| 0 <= i < events.len() ==>
            (#[trigger] events[i])@.len() == 2
            && 1 <= events[i]@[0] <= 100000
            && 1 <= events[i]@[1] <= 100000,
        forall|i: int, j: int|
            0 <= i < j < events.len()
            ==> (#[trigger] events[i])@[1] <= (#[trigger] events[j])@[1],
{
    let n = indices.len();
    let mut events: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            n == indices.len(),
            indices.len() == times.len(),
            1 <= n <= 1000,
            k <= n,
            events.len() == k,
            forall|i: int| 0 <= i < indices.len() ==> 1 <= #[trigger] indices[i] <= 100000,
            forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 100000,
            forall|i: int, j: int| 0 <= i < j < times.len() ==> times[i] <= times[j],
            forall|i: int| 0 <= i < k as int ==>
                (#[trigger] events[i])@.len() == 2
                && events[i]@[0] == indices[i]
                && events[i]@[1] == times[i],
        decreases n - k,
    {
        let mut ev: Vec<i32> = Vec::new();
        ev.push(indices[k]);
        ev.push(times[k]);
        assert(ev@.len() == 2);
        assert(ev@[0] == indices[k as int]);
        assert(ev@[1] == times[k as int]);
        events.push(ev);
        k = k + 1;
    }

    assert forall|i: int, j: int|
        0 <= i < j < events.len()
        implies (#[trigger] events[i])@[1] <= (#[trigger] events[j])@[1]
    by {
        assert(events[i]@[1] == times[i]);
        assert(events[j]@[1] == times[j]);
        assert(times[i] <= times[j]);
    }

    events
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

fn build_sorted_times(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut raw: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random times
            for _ in 0..n {
                raw.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            // all same time
            let t = rng.gen_range_i32(1, 100000);
            for _ in 0..n {
                raw.push(t);
            }
        }
        2 => {
            // strictly increasing by 1 starting from 1
            for i in 0..n {
                let v = ((i + 1) as i32).min(100000);
                raw.push(v);
            }
        }
        3 => {
            // max times
            for _ in 0..n {
                raw.push(100000);
            }
        }
        4 => {
            // min times (all 1)
            for _ in 0..n {
                raw.push(1);
            }
        }
        5 => {
            // small range with duplicates
            for _ in 0..n {
                raw.push(rng.gen_range_i32(1, 10));
            }
        }
        6 => {
            // spread out
            let step = (100000 / (n as i32).max(1)).max(1);
            for i in 0..n {
                let v = ((i as i32 + 1) * step).min(100000).max(1);
                raw.push(v);
            }
        }
        7 => {
            // first one huge, rest random smaller? Must be sorted, so just random
            for _ in 0..n {
                raw.push(rng.gen_range_i32(1, 100000));
            }
        }
        8 => {
            // two distinct times
            let a = rng.gen_range_i32(1, 50000);
            let b = rng.gen_range_i32(50001, 100000);
            for i in 0..n {
                if i < n / 2 {
                    raw.push(a);
                } else {
                    raw.push(b);
                }
            }
        }
        _ => {
            for _ in 0..n {
                raw.push(rng.gen_range_i32(1, 100000));
            }
        }
    }
    raw.sort();
    for v in raw.iter_mut() {
        if *v < 1 { *v = 1; }
        if *v > 100000 { *v = 100000; }
    }
    raw
}

fn build_indices(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut idx: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                idx.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            // all same index
            let x = rng.gen_range_i32(1, 100000);
            for _ in 0..n {
                idx.push(x);
            }
        }
        2 => {
            // all index 1
            for _ in 0..n {
                idx.push(1);
            }
        }
        3 => {
            // small range  1..5
            for _ in 0..n {
                idx.push(rng.gen_range_i32(1, 5));
            }
        }
        4 => {
            // increasing
            for i in 0..n {
                idx.push(((i + 1) as i32).min(100000));
            }
        }
        5 => {
            // max index
            for _ in 0..n {
                idx.push(100000);
            }
        }
        6 => {
            // mix large/small
            for i in 0..n {
                if i % 2 == 0 {
                    idx.push(rng.gen_range_i32(1, 10));
                } else {
                    idx.push(rng.gen_range_i32(99990, 100000));
                }
            }
        }
        _ => {
            for _ in 0..n {
                idx.push(rng.gen_range_i32(1, 100000));
            }
        }
    }
    idx
}

fn print_events(events: &[Vec<i32>]) {
    let events = generate_test_case(events.to_vec());
    print!("{{\"events\":[");
    for i in 0..events.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", events[i][0], events[i][1]);
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

    for t in 0..total {
        let mode_t = t % 10;
        let mode_i = (t / 3) % 7;

        let n: usize = match t % 12 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 1000,
            4 => 999,
            5 => 500,
            6 => 10,
            7 => 50,
            8 => rng.gen_range_usize(1, 20),
            9 => rng.gen_range_usize(100, 300),
            10 => rng.gen_range_usize(1, 1000),
            _ => rng.gen_range_usize(4, 100),
        };

        let times = build_sorted_times(&mut rng, n, mode_t);
        let indices = build_indices(&mut rng, n, mode_i);

        let events = generate_candidate(&indices, &times);
        print_events(&events);
    }
}
