use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: &Vec<i32>,
    durs: &Vec<i32>,
) -> (tasks: Vec<Vec<i32>>)
    requires
        starts.len() == durs.len(),
        1 <= starts.len() <= 100,
        forall |i: int| 0 <= i < starts.len() ==> 1 <= #[trigger] starts[i] <= 100,
        forall |i: int| 0 <= i < durs.len() ==> 1 <= #[trigger] durs[i] <= 100,
    ensures
        1 <= tasks.len() <= 100,
        forall |i: int| 0 <= i < tasks.len() ==> #[trigger] tasks[i].len() == 2
            && 1 <= tasks[i][0] <= 100 && 1 <= tasks[i][1] <= 100,
{
    let n = starts.len();
    let mut tasks: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == starts.len(),
            starts.len() == durs.len(),
            1 <= n <= 100,
            0 <= i <= n,
            tasks.len() == i,
            forall |k: int| 0 <= k < starts.len() ==> 1 <= #[trigger] starts[k] <= 100,
            forall |k: int| 0 <= k < durs.len() ==> 1 <= #[trigger] durs[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> #[trigger] tasks[k].len() == 2
                && 1 <= tasks[k][0] <= 100 && 1 <= tasks[k][1] <= 100,
        decreases n - i,
    {
        let mut t: Vec<i32> = Vec::new();
        t.push(starts[i]);
        t.push(durs[i]);
        assert(t.len() == 2);
        assert(t[0] == starts[i as int]);
        assert(t[1] == durs[i as int]);
        tasks.push(t);
        i = i + 1;
    }
    tasks
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_pair(rng: &mut Rng, mode: usize, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut starts = Vec::with_capacity(n);
    let mut durs = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                starts.push(rng.gen_range_i32(1, 100));
                durs.push(rng.gen_range_i32(1, 100));
            }
        }
        1 => {
            for _ in 0..n {
                starts.push(1);
                durs.push(1);
            }
        }
        2 => {
            for _ in 0..n {
                starts.push(100);
                durs.push(100);
            }
        }
        3 => {
            for i in 0..n {
                starts.push((i as i32 % 100) + 1);
                durs.push(((i as i32 * 7) % 100) + 1);
            }
        }
        4 => {
            // one clearly minimal
            for _ in 0..n {
                starts.push(rng.gen_range_i32(50, 100));
                durs.push(rng.gen_range_i32(50, 100));
            }
            let idx = rng.gen_range_usize(0, n - 1);
            starts[idx] = 1;
            durs[idx] = 1;
        }
        5 => {
            // ties for minimum finish time
            for _ in 0..n {
                let s = rng.gen_range_i32(1, 50);
                starts.push(s);
                durs.push(51 - s + rng.gen_range_i32(0, 0));
            }
        }
        6 => {
            // large start small dur
            for _ in 0..n {
                starts.push(rng.gen_range_i32(90, 100));
                durs.push(rng.gen_range_i32(1, 10));
            }
        }
        7 => {
            // small start large dur
            for _ in 0..n {
                starts.push(rng.gen_range_i32(1, 10));
                durs.push(rng.gen_range_i32(90, 100));
            }
        }
        8 => {
            // first task is minimum
            for _ in 0..n {
                starts.push(rng.gen_range_i32(50, 100));
                durs.push(rng.gen_range_i32(50, 100));
            }
            starts[0] = 1;
            durs[0] = 1;
        }
        9 => {
            // last task is minimum
            for _ in 0..n {
                starts.push(rng.gen_range_i32(50, 100));
                durs.push(rng.gen_range_i32(50, 100));
            }
            starts[n - 1] = 1;
            durs[n - 1] = 1;
        }
        _ => {
            for _ in 0..n {
                starts.push(rng.gen_range_i32(1, 100));
                durs.push(rng.gen_range_i32(1, 100));
            }
        }
    }
    (starts, durs)
}

fn print_json(tasks: &[Vec<i32>]) {
    print!("{{\"tasks\":[");
    for i in 0..tasks.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", tasks[i][0], tasks[i][1]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 100),
            1 => 100,
            2 => 1,
            3 => 50,
            4 => 2 + (t % 50),
            5 => 10,
            6 => 25,
            7 => 75,
            8 => 100,
            9 => 100,
            _ => 1 + (t % 100),
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let (starts, durs) = build_pair(&mut rng, mode, n);
        let tasks = generate_test_case(&starts, &durs);
        print_json(&tasks);
    }
}