use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 50,
    ensures
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        nums@ == values@,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 50,
        decreases values.len() - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    assert(nums@ =~= values@);
    nums
}

}

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

fn build_values(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    // Build list of length n where each value in 1..=max_val appears at most twice.
    // Strategy: pool of candidates with counts.
    let mv = max_val.max(1) as usize;
    let mut counts: Vec<u8> = vec![0u8; mv + 1];
    let mut out: Vec<i32> = Vec::with_capacity(n);
    let mut attempts = 0usize;
    while out.len() < n && attempts < 10_000 {
        attempts += 1;
        let v = rng.gen_range(1, mv);
        if counts[v] < 2 {
            counts[v] += 1;
            out.push(v as i32);
        }
    }
    // Fallback: fill remaining with any value still having count < 2.
    while out.len() < n {
        let mut placed = false;
        for v in 1..=mv {
            if counts[v] < 2 {
                counts[v] += 1;
                out.push(v as i32);
                placed = true;
                break;
            }
        }
        if !placed {
            break;
        }
    }
    // Clamp final length to [1, 50].
    if out.is_empty() {
        out.push(1);
    }
    if out.len() > 50 {
        out.truncate(50);
    }
    out
}

fn adversarial(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![1],
        1 => vec![50],
        2 => vec![1, 1],
        3 => vec![50, 50],
        4 => {
            // All 50 values once each.
            let mut v = Vec::new();
            for i in 1..=50 { v.push(i as i32); }
            v
        }
        5 => {
            // 25 distinct values, each twice (length 50).
            let mut v = Vec::new();
            for i in 1..=25 {
                v.push(i as i32);
                v.push(i as i32);
            }
            v
        }
        6 => {
            // Mix: half duplicated, half unique.
            let mut v = Vec::new();
            for i in 1..=10 {
                v.push(i as i32);
                v.push(i as i32);
            }
            for i in 11..=30 {
                v.push(i as i32);
            }
            v
        }
        7 => {
            // Single duplicated value scattered.
            let mut v = vec![7, 3, 5, 7, 2, 8, 4];
            v
        }
        8 => {
            // Boundaries duplicated: 1 and 50.
            let mut v = vec![1, 50, 1, 50, 2, 3];
            v
        }
        9 => {
            // Random small.
            let n = rng.gen_range(1, 10);
            build_values(rng, n, 50)
        }
        10 => {
            let n = rng.gen_range(40, 50);
            build_values(rng, n, 50)
        }
        _ => {
            let n = rng.gen_range(1, 50);
            let mv = rng.gen_range(1, 50) as i32;
            build_values(rng, n, mv)
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
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
    let modes = 12usize;

    for t in 0..total {
        let mode = if t < modes * 2 { t % modes } else { 11 };
        let values = adversarial(&mut rng, mode);
        // Safety filter: ensure constraints hold.
        let mut ok = !values.is_empty() && values.len() <= 50;
        if ok {
            let mut counts = [0i32; 51];
            for &x in &values {
                if x < 1 || x > 50 { ok = false; break; }
                counts[x as usize] += 1;
                if counts[x as usize] > 2 { ok = false; break; }
            }
        }
        let final_values = if ok {
            values
        } else {
            vec![1]
        };
        let nums = generate_test_case(&final_values);
        print_json(&nums);
    }
}