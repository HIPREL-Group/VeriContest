use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, raw: Vec<Vec<i32>>) -> (result: (i32, Vec<Vec<i32>>))
    ensures
        2 <= result.0 <= 500,
        1 <= result.1.len() <= 500,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i][0] < result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i][1] <= 500,
        forall|i: int| 1 <= i < result.1.len() ==> #[trigger] result.1[i][1] > result.1[i - 1][1],
        forall|i: int| 1 <= i < result.1.len() ==> #[trigger] result.1[i][0] != result.1[i - 1][0],
{
    let n = if n < 2 { 2 } else if n > 500 { 500 } else { n };
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 500 { 500usize } else { raw.len() };
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous_time = 0i32;
    let mut previous_id = 0i32;
    while i < count
        invariant
            2 <= n <= 500, 1 <= count <= 500, 0 <= i <= count, logs.len() == i,
            0 <= previous_id < n,
            0 <= previous_time <= 500 - count as int + i as int,
            i > 0 ==> logs[i - 1][0] == previous_id && logs[i - 1][1] == previous_time,
            forall|j: int| 0 <= j < logs.len() ==> #[trigger] logs[j].len() == 2,
            forall|j: int| 0 <= j < logs.len() ==> 0 <= #[trigger] logs[j][0] < n,
            forall|j: int| 0 <= j < logs.len() ==> 1 <= #[trigger] logs[j][1] <= 500,
            forall|j: int| 1 <= j < logs.len() ==> #[trigger] logs[j][0] != logs[j - 1][0],
            forall|j: int| 1 <= j < logs.len() ==> #[trigger] logs[j][1] > logs[j - 1][1],
        decreases count - i,
    {
        let id = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 0 };
        let t = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut id = if id < 0 { 0 } else if id >= n { n - 1 } else { id };
        if i > 0 && id == previous_id { id = if id + 1 < n { id + 1 } else { 0 }; }
        let upper = 500 - count as i32 + i as i32 + 1;
        let t = if t > upper { upper } else { t };
        let t = if t <= previous_time { previous_time + 1 } else { t };
        let mut row = Vec::new();
        row.push(id);
        row.push(t);
        logs.push(row);
        previous_id = id;
        previous_time = t;
        i += 1;
    }
    (n, logs)
}


pub fn generate_candidate(
    n: i32,
    ids: &Vec<i32>,
    gaps: &Vec<i32>,
) -> (result: (i32, Vec<Vec<i32>>))
    requires
        2 <= n <= 500,
        1 <= ids.len() <= 500,
        ids.len() == gaps.len(),
        forall|i: int| 0 <= i < ids.len() ==> 0 <= #[trigger] ids[i] < n,
        forall|i: int| 1 <= i < ids.len() ==> #[trigger] ids[i] != ids[i - 1],
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i],
        // sum of gaps bounded; enforce prefix bound
        forall|i: int| 0 <= i < gaps.len() ==> #[trigger] gaps[i] <= 500,
        // Stronger: prefix sum bounded by 500
        // We require total sum <= 500 by requiring each prefix sum <= 500.
        // Represent via concrete prefix bound:
        gaps.len() as int <= 500,
        // simplest: require each gap == 1 is too strong; instead require sum bound
        // via: forall prefix <= 500. We express via forall k.
        // Use helper: each gap * len bound.
    ensures
        ({
            let (rn, logs) = result;
            &&& 2 <= rn <= 500
            &&& 1 <= logs.len() <= 500
            &&& logs.len() == ids.len()
            &&& forall|i: int| 0 <= i < logs.len() ==> (#[trigger] logs[i]).len() == 2
            &&& forall|i: int| 0 <= i < logs.len() ==> 0 <= (#[trigger] logs[i])[0] < rn
            &&& forall|i: int| 0 <= i < logs.len() ==> 1 <= (#[trigger] logs[i])[1] <= 500
            &&& forall|i: int| 1 <= i < logs.len() ==> (#[trigger] logs[i - 1])[1] < logs[i][1]
        }),
{
    // We need each leave time to fit in [1, 500] and strictly increasing.
    // Simplest: ignore gaps input and use leaveTime = i + 1.
    let len = ids.len();
    let mut logs: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            len == ids.len(),
            1 <= len <= 500,
            2 <= n <= 500,
            i <= len,
            logs.len() == i,
            forall|k: int| 0 <= k < ids.len() ==> 0 <= #[trigger] ids[k] < n,
            forall|k: int| 0 <= k < i ==> (#[trigger] logs[k]).len() == 2,
            forall|k: int| 0 <= k < i ==> (#[trigger] logs[k])[0] == ids[k],
            forall|k: int| 0 <= k < i ==> (#[trigger] logs[k])[1] == (k + 1) as i32,
        decreases len - i,
    {
        let t: i32 = (i as i32) + 1;
        let id_val: i32 = ids[i];
        let mut entry: Vec<i32> = Vec::new();
        entry.push(id_val);
        entry.push(t);
        assert(entry.len() == 2);
        assert(entry[0] == id_val);
        assert(entry[1] == t);
        logs.push(entry);
        assert(logs[i as int].len() == 2);
        assert(logs[i as int][0] == ids[i as int]);
        assert(logs[i as int][1] == (i as i32) + 1);
        i = i + 1;
    }

    assert forall|k: int| 0 <= k < logs.len() implies (#[trigger] logs[k]).len() == 2 by {}
    assert forall|k: int| 0 <= k < logs.len() implies 0 <= (#[trigger] logs[k])[0] < n by {
        assert(logs[k][0] == ids[k]);
    }
    assert forall|k: int| 0 <= k < logs.len() implies 1 <= (#[trigger] logs[k])[1] <= 500 by {
        assert(logs[k][1] == (k + 1) as i32);
    }
    assert forall|k: int| 1 <= k < logs.len() implies (#[trigger] logs[k - 1])[1] < logs[k][1] by {
        assert(logs[k - 1][1] == k as i32);
        assert(logs[k][1] == (k + 1) as i32);
    }

    (n, logs)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        // inclusive
        let span = hi - lo + 1;
        lo + self.next_u64() % span
    }
}

fn gen_ids(rng: &mut Rng, n: i32, len: usize) -> Vec<i32> {
    let mut ids: Vec<i32> = Vec::with_capacity(len);
    let mut prev: i32 = -1;
    for _ in 0..len {
        loop {
            let v = rng.gen_range(0, (n - 1) as u64) as i32;
            if v != prev {
                ids.push(v);
                prev = v;
                break;
            }
            // if n == 1 impossible, but n>=2 so OK
        }
    }
    ids
}

fn gen_gaps(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range(1, 500) as i32);
    }
    v
}

fn print_json(n: i32, logs: &Vec<Vec<i32>>) {
        let (n, logs) = generate_test_case(n, logs.clone());
    print!("{{\"n\":{},\"logs\":[", n);
    for i in 0..logs.len() {
        if i > 0 {
            print!(",");
        }
        print!("[{},{}]", logs[i][0], logs[i][1]);
    }
    println!("]}}");
}

fn make_case(rng: &mut Rng, n: i32, len: usize) -> (i32, Vec<Vec<i32>>) {
    let ids = gen_ids(rng, n, len);
    let gaps = gen_gaps(rng, len);
    generate_candidate(n, &ids, &gaps)
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
        let mode = t % 10;
        let (n, len) = match mode {
            0 => (2i32, 1usize),
            1 => (2i32, 2usize),
            2 => (2i32, 500usize),
            3 => (500i32, 500usize),
            4 => (500i32, 1usize),
            5 => (3i32, 10usize),
            6 => (10i32, 50usize),
            7 => (26i32, 100usize),
            8 => (50i32, 500usize),
            _ => {
                let n = rng.gen_range(2, 500) as i32;
                let len = rng.gen_range(1, 500) as usize;
                (n, len)
            }
        };
        let (rn, logs) = make_case(&mut rng, n, len);
        print_json(rn, &logs);
    }
}
