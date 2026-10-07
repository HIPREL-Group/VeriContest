use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: &Vec<i32>,
    ends: &Vec<i32>,
) -> (result: Vec<Vec<i32>>)
    requires
        starts.len() == ends.len(),
        1 <= starts.len() <= 100,
        forall|i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= ends[i] <= 100,
        forall|i: int| 0 <= i < ends.len() ==> 1 <= starts[i] <= #[trigger] ends[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i][0],
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i][0] <= result[i][1],
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i][1] <= 100,
{
    let n = starts.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            n == starts.len(),
            starts.len() == ends.len(),
            1 <= starts.len() <= 100,
            0 <= idx <= n,
            result.len() == idx,
            forall|i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= ends[i] <= 100,
            forall|k: int| 0 <= k < idx as int ==> #[trigger] result[k].len() == 2,
            forall|k: int| 0 <= k < idx as int ==> (#[trigger] result[k])[0] == starts[k],
            forall|k: int| 0 <= k < idx as int ==> (#[trigger] result[k])[1] == ends[k],
        decreases n - idx,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(starts[idx]);
        pair.push(ends[idx]);
        assert(pair.len() == 2);
        assert(pair[0] == starts[idx as int]);
        assert(pair[1] == ends[idx as int]);
        result.push(pair);
        idx = idx + 1;
    }

    result
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build(starts: Vec<i32>, ends: Vec<i32>) -> Vec<Vec<i32>> {
    generate_test_case(&starts, &ends)
}

fn print_json(nums: &Vec<Vec<i32>>) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", nums[i][0], nums[i][1]);
    }
    println!("]}}");
}

fn make_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    let mut starts: Vec<i32> = Vec::new();
    let mut ends: Vec<i32> = Vec::new();

    match mode {
        0 => {
            // Single car
            let s = rng.gen_range_i32(1, 100);
            let e = rng.gen_range_i32(s, 100);
            starts.push(s);
            ends.push(e);
        }
        1 => {
            // All cars cover the whole range [1,100]
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                starts.push(1);
                ends.push(100);
            }
        }
        2 => {
            // All cars are single points
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                let p = rng.gen_range_i32(1, 100);
                starts.push(p);
                ends.push(p);
            }
        }
        3 => {
            // Disjoint cars
            let n = rng.gen_range_usize(1, 50);
            let mut cur: i32 = 1;
            for _ in 0..n {
                if cur > 100 {
                    starts.push(100);
                    ends.push(100);
                } else {
                    let s = cur;
                    let remain = 100 - s;
                    let len = if remain > 0 { rng.gen_range_i32(0, remain.min(3)) } else { 0 };
                    let e = s + len;
                    starts.push(s);
                    ends.push(e);
                    cur = e + 2;
                }
            }
        }
        4 => {
            // Overlapping cars
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 50);
                let e = rng.gen_range_i32(50, 100);
                starts.push(s);
                ends.push(e);
            }
        }
        5 => {
            // Edge: all at 1
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                starts.push(1);
                ends.push(1);
            }
        }
        6 => {
            // Edge: all at 100
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                starts.push(100);
                ends.push(100);
            }
        }
        7 => {
            // Duplicates
            let n = rng.gen_range_usize(1, 100);
            let s = rng.gen_range_i32(1, 100);
            let e = rng.gen_range_i32(s, 100);
            for _ in 0..n {
                starts.push(s);
                ends.push(e);
            }
        }
        8 => {
            // Max length
            for _ in 0..100 {
                let s = rng.gen_range_i32(1, 100);
                let e = rng.gen_range_i32(s, 100);
                starts.push(s);
                ends.push(e);
            }
        }
        9 => {
            // Adjacent intervals (touching)
            let n = rng.gen_range_usize(1, 50);
            let mut cur: i32 = 1;
            for _ in 0..n {
                if cur > 100 {
                    starts.push(100);
                    ends.push(100);
                } else {
                    let s = cur;
                    let remain = 100 - s;
                    let len = if remain > 0 { rng.gen_range_i32(0, remain.min(5)) } else { 0 };
                    let e = s + len;
                    starts.push(s);
                    ends.push(e);
                    cur = e + 1;
                }
            }
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 100);
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 100);
                let e = rng.gen_range_i32(s, 100);
                starts.push(s);
                ends.push(e);
            }
        }
    }

    if starts.is_empty() {
        starts.push(1);
        ends.push(1);
    }

    (starts, ends)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (starts, ends) = make_case(&mut rng, mode);
        let nums = build(starts, ends);
        print_json(&nums);
    }
}