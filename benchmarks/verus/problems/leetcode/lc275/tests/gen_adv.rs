use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, start: i32) -> (citations: Vec<i32>)
    requires
        1 <= n <= 5000,
        0 <= start,
        start as int + n as int <= 1_001,
    ensures
        1 <= citations.len() <= 5_000,
        forall |i: int| 0 <= i < citations.len() ==> 0 <= #[trigger] citations[i] <= 1_000,
        forall |i: int, j: int| 0 <= i < j < citations.len() ==> citations[i] < citations[j],
{
    let mut citations: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            1 <= n <= 5000,
            0 <= start,
            start as int + n as int <= 1_001,
            citations.len() == k,
            forall |i: int| 0 <= i < k as int ==> citations[i] == start as int + i,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] citations[i] <= 1_000,
        decreases n - k,
    {
        let v: i32 = start + (k as i32);
        assert(v as int == start as int + k as int);
        assert(0 <= v <= 1_000);
        citations.push(v);
        k = k + 1;
    }

    assert forall |i: int, j: int| 0 <= i < j < citations.len() implies citations[i] < citations[j] by {
        assert(citations[i] == start as int + i);
        assert(citations[j] == start as int + j);
    }

    citations
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn print_json(citations: &[i32]) {
    print!("{{\"citations\":[");
    for i in 0..citations.len() {
        if i > 0 { print!(","); }
        print!("{}", citations[i]);
    }
    println!("]}}");
}

fn make_case(n: usize, start: i32) -> Vec<i32> {
    // Enforce ensures clauses; clamp
    let mut nn = n;
    if nn < 1 { nn = 1; }
    if nn > 5000 { nn = 5000; }
    let max_start = 1001i32 - (nn as i32);
    let mut s = start;
    if s < 0 { s = 0; }
    if s > max_start { s = max_start; }
    generate_test_case(nn, s)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        let (n, start) = match mode {
            0 => (1usize, 0i32),                    // smallest, all zero
            1 => (1usize, 1000i32),                 // smallest, max cit
            2 => (2usize, 0i32),                    // start at 0
            3 => (5usize, 0i32),                    // example-like
            4 => (1001usize, 0i32),                 // max span from 0
            5 => {                                  // random small
                let n = rng.gen_range(1, 50);
                let max_start = 1001i32 - (n as i32);
                let s = rng.gen_range(0, max_start.max(0) as usize) as i32;
                (n, s)
            }
            6 => {                                  // random medium
                let n = rng.gen_range(50, 500);
                let max_start = 1001i32 - (n as i32);
                let s = rng.gen_range(0, max_start.max(0) as usize) as i32;
                (n, s)
            }
            7 => {                                  // random large (capped by range)
                let n = rng.gen_range(500, 1001);
                let max_start = 1001i32 - (n as i32);
                let s = rng.gen_range(0, max_start.max(0) as usize) as i32;
                (n, s)
            }
            8 => (1001usize, 0i32),                 // full 0..1000
            _ => {
                let n = rng.gen_range(2, 100);
                let max_start = 1001i32 - (n as i32);
                let s = rng.gen_range(0, max_start.max(0) as usize) as i32;
                (n, s)
            }
        };

        let c = make_case(n, start);
        print_json(&c);
    }
}