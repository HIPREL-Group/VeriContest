use vstd::prelude::*;

verus! {

pub open spec fn spec_prefix_sum(seq: Seq<i32>, k: int) -> int
    recommends 0 <= k <= seq.len(),
    decreases k,
{
    if k <= 0 {
        0
    } else {
        spec_prefix_sum(seq, k - 1) + seq[k - 1] as int
    }
}

pub proof fn lemma_prefix_sum_bound(s: Seq<i32>, k: int)
    requires
        0 <= k <= s.len(),
        forall |i: int| 0 <= i < s.len() ==> 0 <= (#[trigger] s[i]) as int <= 8,
    ensures
        0 <= spec_prefix_sum(s, k) <= 8 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_prefix_sum_bound(s, k - 1);
    }
}

pub fn generate_test_case(
    d: usize,
    sum_time: i32,
    mins: &Vec<i32>,
    maxs: &Vec<i32>,
) -> (res: (usize, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= d <= 30,
        mins.len() == d,
        maxs.len() == d,
        0 <= sum_time <= 240,
        forall |i: int| 0 <= i < d as int ==>
            0 <= (#[trigger] mins[i]) as int <= (maxs[i] as int) <= 8,
    ensures
        res.0 == d,
        res.1 == sum_time,
        res.2.len() == d,
        res.3.len() == d,
        0 <= res.1 <= 240,
        1 <= res.0 <= 30,
        forall |i: int| 0 <= i < res.0 as int ==>
            0 <= (#[trigger] res.2@[i]) as int <= (res.3@[i] as int) <= 8,
{
    let mut min_t: Vec<i32> = Vec::new();
    let mut max_t: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < d
        invariant
            0 <= i <= d,
            min_t.len() == i,
            max_t.len() == i,
            mins.len() == d,
            maxs.len() == d,
            forall |k: int| 0 <= k < i as int ==>
                (#[trigger] min_t@[k]) == mins[k] && max_t@[k] == maxs[k],
            forall |k: int| 0 <= k < d as int ==>
                0 <= (#[trigger] mins[k]) as int <= (maxs[k] as int) <= 8,
        decreases d - i,
    {
        min_t.push(mins[i]);
        max_t.push(maxs[i]);
        i = i + 1;
    }

    (d, sum_time, min_t, max_t)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (usize, i32, Vec<i32>, Vec<i32>) {
    let d: usize = match mode {
        0 => 1,
        1 => 30,
        2 => rng.gen_range_usize(1, 5),
        3 => rng.gen_range_usize(1, 30),
        _ => rng.gen_range_usize(1, 30),
    };

    let mut mins: Vec<i32> = Vec::new();
    let mut maxs: Vec<i32> = Vec::new();

    let mut sum_min: i32 = 0;
    let mut sum_max: i32 = 0;

    for _ in 0..d {
        let mn = rng.gen_range_i32(0, 8);
        let mx = rng.gen_range_i32(mn, 8);
        mins.push(mn);
        maxs.push(mx);
        sum_min += mn;
        sum_max += mx;
    }

    let sum_time: i32 = match mode {
        0 => 0,
        1 => 240,
        2 => {
            // exactly feasible
            if sum_min <= 240 {
                let hi = if sum_max < 240 { sum_max } else { 240 };
                if sum_min <= hi {
                    rng.gen_range_i32(sum_min, hi)
                } else {
                    sum_min.min(240)
                }
            } else {
                0
            }
        }
        3 => {
            // exactly sum_min
            sum_min.min(240)
        }
        4 => {
            // exactly sum_max
            sum_max.min(240)
        }
        5 => {
            // just below min (infeasible)
            if sum_min > 0 { (sum_min - 1).max(0).min(240) } else { 0 }
        }
        6 => {
            // just above max (infeasible)
            if sum_max < 240 { sum_max + 1 } else { 240 }
        }
        7 => {
            rng.gen_range_i32(0, 240)
        }
        8 => {
            // boundary: exactly feasible endpoint
            if sum_min <= 240 { sum_min.min(240) } else { 240 }
        }
        9 => {
            if sum_max <= 240 { sum_max } else { 240 }
        }
        _ => rng.gen_range_i32(0, 240),
    };

    let sum_time = sum_time.max(0).min(240);
    (d, sum_time, mins, maxs)
}

fn print_json(d: usize, sum_time: i32, mins: &Vec<i32>, maxs: &Vec<i32>) {
    print!("{{\"d\":{},\"sum_time\":{},\"min_t\":[", d, sum_time);
    for i in 0..mins.len() {
        if i > 0 { print!(","); }
        print!("{}", mins[i]);
    }
    print!("],\"max_t\":[");
    for i in 0..maxs.len() {
        if i > 0 { print!(","); }
        print!("{}", maxs[i]);
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (d, sum_time, mins, maxs) = build_case(&mut rng, mode);
        let (d2, st2, mt, mxt) = generate_test_case(d, sum_time, &mins, &maxs);
        print_json(d2, st2, &mt, &mxt);
    }
}