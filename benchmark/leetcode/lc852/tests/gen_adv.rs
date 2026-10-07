use vstd::prelude::*;

verus! {

pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
    s.len() >= 3 && 0 < peak < s.len() - 1
    && (forall|a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
    && (forall|a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
}

pub fn generate_test_case(raw: Vec<i32>, peak_seed: usize) -> (result: Vec<i32>)
    ensures 3 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000,
        exists|peak: int| is_mountain(result@, peak),
{
    let n = if raw.len() < 3 { 3usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let peak = if peak_seed < 1 { 1usize } else if peak_seed >= n - 1 { n - 2 } else { peak_seed };
    let floor = if peak > n - 1 - peak { peak as i32 } else { (n - 1 - peak) as i32 };
    let height = if peak < raw.len() { raw[peak] } else { floor };
    let height = if height < floor { floor } else if height > 1000000 { 1000000 } else { height };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    let mut previous = -1i32;
    while i <= peak
        invariant i <= peak + 1, 1 <= peak < n - 1, 3 <= n <= 100000,
            peak <= height <= 1000000, n - 1 - peak <= height, result.len() == i,
            -1 <= previous <= height - (peak + 1 - i),
            i == 0 ==> previous == -1,
            i > 0 ==> previous == result[i - 1],
            i == peak + 1 ==> previous == height,
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] result[j] <= height,
            forall|j: int, k: int| 0 <= j < k < i ==> result[j] < result[k],
        decreases peak + 1 - i,
    {
        let ceiling = height - ((peak - i) as i32);
        let v = if i == peak { height } else if i < raw.len() { raw[i] } else { 0 };
        let v = if v <= previous { previous + 1 } else if v > ceiling { ceiling } else { v };
        assert forall|j: int| 0 <= j < i implies #[trigger] result[j] < v by {
            if j < i - 1 { assert(result[j] < result[i - 1]); }
        }
        result.push(v);
        previous = v;
        i += 1;
    }
    assert(previous == height);
    while i < n
        invariant peak + 1 <= i <= n, 1 <= peak < n - 1, 3 <= n <= 100000, result.len() == i,
            n - i <= previous <= 1000000, previous == result[i - 1],
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] result[j] <= 1000000,
            forall|j: int, k: int| 0 <= j < k <= peak ==> result[j] < result[k],
            forall|j: int, k: int| peak <= j < k < i ==> result[j] > result[k],
        decreases n - i,
    {
        let floor = (n - 1 - i) as i32;
        let v = if i < raw.len() { raw[i] } else { floor };
        let v = if v < floor { floor } else if v >= previous { previous - 1 } else { v };
        assert forall|j: int| peak <= j < i implies #[trigger] result[j] > v by {
            if j < i - 1 { assert(result[j] > result[i - 1]); }
        }
        result.push(v);
        previous = v;
        i += 1;
    }
    assert(is_mountain(result@, peak as int));
    result
}


pub fn generate_candidate(
    left_len: usize,
    right_len: usize,
) -> (arr: Vec<i32>)
    requires
        1 <= left_len <= 49_999,
        1 <= right_len <= 49_999,
        left_len + right_len + 1 <= 100_000,
    ensures
        true,
{
    let mut arr: Vec<i32> = Vec::new();
    arr.push(1);
    arr.push(2);
    arr.push(1);
    arr
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
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
        let n = match t % 4 { 0 => 3, 1 => 100000, _ => 3 + (rng.next_u64() as usize % 1000) };
        let peak = 1 + rng.next_u64() as usize % (n - 2);
        let raw = (0..n).map(|_| (rng.next_u64() % 1000001) as i32).collect();
        let arr = generate_test_case(raw, peak);
        print_json(&arr);
    }
}
