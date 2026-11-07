use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    gas_vals: &Vec<i32>,
    cost_vals: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        gas_vals.len() == cost_vals.len(),
        1 <= gas_vals.len() <= 100_000,
        forall|i: int| 0 <= i < gas_vals.len() ==> 0 <= #[trigger] gas_vals[i] <= 10_000,
        forall|i: int| 0 <= i < cost_vals.len() ==> 0 <= #[trigger] cost_vals[i] <= 10_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10_000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 10_000,
{
    let n = gas_vals.len();
    let mut gas: Vec<i32> = Vec::new();
    let mut cost: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == gas_vals.len(),
            n == cost_vals.len(),
            1 <= n <= 100_000,
            0 <= i <= n,
            gas.len() == i,
            cost.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] gas[k] == gas_vals[k],
            forall|k: int| 0 <= k < i as int ==> #[trigger] cost[k] == cost_vals[k],
            forall|k: int| 0 <= k < gas_vals.len() ==> 0 <= #[trigger] gas_vals[k] <= 10_000,
            forall|k: int| 0 <= k < cost_vals.len() ==> 0 <= #[trigger] cost_vals[k] <= 10_000,
        decreases n - i,
    {
        gas.push(gas_vals[i]);
        cost.push(cost_vals[i]);
        i = i + 1;
    }
    (gas, cost)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // tiny n=1
            let g = rng.gen_range_i32(0, 10_000);
            let c = rng.gen_range_i32(0, 10_000);
            (vec![g], vec![c])
        }
        1 => {
            // n=2 small
            let g = vec![rng.gen_range_i32(0, 10), rng.gen_range_i32(0, 10)];
            let c = vec![rng.gen_range_i32(0, 10), rng.gen_range_i32(0, 10)];
            (g, c)
        }
        2 => {
            // gas == cost everywhere
            let n = rng.gen_range_usize(1, 100);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                let v = rng.gen_range_i32(0, 10_000);
                g.push(v);
                c.push(v);
            }
            (g, c)
        }
        3 => {
            // impossible: cost > gas each
            let n = rng.gen_range_usize(1, 50);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                let gv = rng.gen_range_i32(0, 5_000);
                g.push(gv);
                c.push(rng.gen_range_i32(gv + 1, 10_000.min(gv + 5_000)));
            }
            (g, c)
        }
        4 => {
            // the leetcode example
            (vec![1,2,3,4,5], vec![3,4,5,1,2])
        }
        5 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            (vec![0; n], vec![0; n])
        }
        6 => {
            // large n random
            let n = 1000 + (t % 500);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                g.push(rng.gen_range_i32(0, 10_000));
                c.push(rng.gen_range_i32(0, 10_000));
            }
            (g, c)
        }
        7 => {
            // maximum n
            let n = 100_000;
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                g.push(rng.gen_range_i32(0, 10_000));
                c.push(rng.gen_range_i32(0, 10_000));
            }
            (g, c)
        }
        8 => {
            // gas dominates heavily
            let n = rng.gen_range_usize(1, 200);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                g.push(rng.gen_range_i32(5_000, 10_000));
                c.push(rng.gen_range_i32(0, 5_000));
            }
            (g, c)
        }
        9 => {
            // cost dominates heavily
            let n = rng.gen_range_usize(1, 200);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                g.push(rng.gen_range_i32(0, 5_000));
                c.push(rng.gen_range_i32(5_000, 10_000));
            }
            (g, c)
        }
        10 => {
            // one big gas station, others just cost
            let n = rng.gen_range_usize(3, 100);
            let mut g = vec![0i32; n];
            let mut c = vec![0i32; n];
            let idx = rng.gen_range_usize(0, n - 1);
            g[idx] = 10_000;
            for i in 0..n {
                c[i] = rng.gen_range_i32(0, 100);
            }
            (g, c)
        }
        _ => {
            // random medium
            let n = rng.gen_range_usize(1, 500);
            let mut g = Vec::new();
            let mut c = Vec::new();
            for _ in 0..n {
                g.push(rng.gen_range_i32(0, 10_000));
                c.push(rng.gen_range_i32(0, 10_000));
            }
            (g, c)
        }
    }
}

fn print_json(gas: &[i32], cost: &[i32]) {
    print!("{{\"gas\":[");
    for i in 0..gas.len() {
        if i > 0 { print!(","); }
        print!("{}", gas[i]);
    }
    print!("],\"cost\":[");
    for i in 0..cost.len() {
        if i > 0 { print!(","); }
        print!("{}", cost[i]);
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
    let modes = 12usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (g, c) = build_mode(&mut rng, mode, t);
        // Guard: ensure len >= 1 and <= 100000 and values in range (they already are by construction).
        if g.len() < 1 || g.len() > 100_000 || g.len() != c.len() {
            continue;
        }
        let mut ok = true;
        for v in &g { if *v < 0 || *v > 10_000 { ok = false; break; } }
        if ok { for v in &c { if *v < 0 || *v > 10_000 { ok = false; break; } } }
        if !ok { continue; }
        let (gg, cc) = generate_test_case(&g, &c);
        print_json(&gg, &cc);
    }
}