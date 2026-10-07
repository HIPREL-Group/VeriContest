use vstd::prelude::*;

verus! {

pub open spec fn count_value_prefix(colsum: Seq<i32>, value: i32, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        count_value_prefix(colsum, value, end - 1) + if colsum[end - 1] == value { 1int } else { 0int }
    }
}

pub fn generate_test_case(
    twos_count: usize,
    ones_in_upper: usize,
    ones_in_lower: usize,
    zeros_count: usize,
) -> (result: (i32, i32, Vec<i32>))
    requires
        twos_count + ones_in_upper + ones_in_lower + zeros_count >= 1,
        twos_count + ones_in_upper + ones_in_lower + zeros_count <= 100_000,
        twos_count <= 100_000,
        ones_in_upper <= 100_000,
        ones_in_lower <= 100_000,
        zeros_count <= 100_000,
    ensures
        ({
            let (upper, lower, colsum) = result;
            &&& 1 <= colsum.len() <= 100_000
            &&& 0 <= upper <= colsum.len()
            &&& 0 <= lower <= colsum.len()
            &&& forall|i: int| 0 <= i < colsum.len() ==> 0 <= #[trigger] colsum[i] <= 2
        }),
{
    let n: usize = twos_count + ones_in_upper + ones_in_lower + zeros_count;
    let upper: i32 = (twos_count + ones_in_upper) as i32;
    let lower: i32 = (twos_count + ones_in_lower) as i32;

    let mut colsum: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < twos_count
        invariant
            colsum.len() == i,
            i <= twos_count,
            forall|k: int| 0 <= k < colsum.len() ==> #[trigger] colsum[k] == 2,
        decreases twos_count - i,
    {
        colsum.push(2);
        i += 1;
    }

    let mut i: usize = 0;
    while i < ones_in_upper
        invariant
            colsum.len() == twos_count + i,
            i <= ones_in_upper,
            forall|k: int| 0 <= k < colsum.len() ==> 0 <= #[trigger] colsum[k] <= 2,
        decreases ones_in_upper - i,
    {
        colsum.push(1);
        i += 1;
    }

    let mut i: usize = 0;
    while i < ones_in_lower
        invariant
            colsum.len() == twos_count + ones_in_upper + i,
            i <= ones_in_lower,
            forall|k: int| 0 <= k < colsum.len() ==> 0 <= #[trigger] colsum[k] <= 2,
        decreases ones_in_lower - i,
    {
        colsum.push(1);
        i += 1;
    }

    let mut i: usize = 0;
    while i < zeros_count
        invariant
            colsum.len() == twos_count + ones_in_upper + ones_in_lower + i,
            i <= zeros_count,
            forall|k: int| 0 <= k < colsum.len() ==> 0 <= #[trigger] colsum[k] <= 2,
        decreases zeros_count - i,
    {
        colsum.push(0);
        i += 1;
    }

    assert(colsum.len() == n);
    assert(n >= 1);
    assert(upper as int == twos_count + ones_in_upper);
    assert(lower as int == twos_count + ones_in_lower);
    assert(upper as int <= n);
    assert(lower as int <= n);

    (upper, lower, colsum)
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

    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        if lo >= hi {
            return lo;
        }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn print_json(upper: i32, lower: i32, colsum: &[i32]) {
    print!("{{\"upper\":{},\"lower\":{},\"colsum\":[", upper, lower);
    for i in 0..colsum.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", colsum[i]);
    }
    println!("]}}");
}

fn clamp_params(twos: usize, oneu: usize, onel: usize, zeros: usize) -> (usize, usize, usize, usize) {
    // Ensure total between 1 and 100_000 and each at most 100_000
    let total = twos + oneu + onel + zeros;
    if total == 0 {
        return (0, 0, 0, 1);
    }
    if total > 100_000 {
        // scale down proportionally - just cap
        let max_each = 25_000;
        let t = twos.min(max_each);
        let u = oneu.min(max_each);
        let l = onel.min(max_each);
        let z = zeros.min(max_each);
        let total2 = t + u + l + z;
        if total2 == 0 {
            return (0, 0, 0, 1);
        }
        return (t, u, l, z);
    }
    (twos, oneu, onel, zeros)
}

fn gen_for_mode(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, usize, usize) {
    let params = match mode {
        0 => {
            // Small random
            let twos = rng.gen_range(0, 5);
            let oneu = rng.gen_range(0, 5);
            let onel = rng.gen_range(0, 5);
            let zeros = rng.gen_range(0, 5);
            (twos, oneu, onel, zeros)
        }
        1 => {
            // All twos
            let twos = rng.gen_range(1, 100);
            (twos, 0, 0, 0)
        }
        2 => {
            // All zeros
            let zeros = rng.gen_range(1, 100);
            (0, 0, 0, zeros)
        }
        3 => {
            // All ones upper only
            let oneu = rng.gen_range(1, 100);
            (0, oneu, 0, 0)
        }
        4 => {
            // All ones lower only
            let onel = rng.gen_range(1, 100);
            (0, 0, onel, 0)
        }
        5 => {
            // Large size near limit
            let twos = rng.gen_range(0, 25_000);
            let oneu = rng.gen_range(0, 25_000);
            let onel = rng.gen_range(0, 25_000);
            let zeros = rng.gen_range(0, 25_000);
            (twos, oneu, onel, zeros)
        }
        6 => {
            // n = 1
            let pick = rng.gen_range(0, 3);
            match pick {
                0 => (1, 0, 0, 0),
                1 => (0, 1, 0, 0),
                2 => (0, 0, 1, 0),
                _ => (0, 0, 0, 1),
            }
        }
        7 => {
            // only twos and zeros
            let twos = rng.gen_range(1, 50);
            let zeros = rng.gen_range(0, 50);
            (twos, 0, 0, zeros)
        }
        8 => {
            // balanced ones
            let k = rng.gen_range(1, 100);
            (0, k, k, 0)
        }
        9 => {
            // edge: upper = 0 but lots of ones going to lower
            let onel = rng.gen_range(1, 100);
            let zeros = rng.gen_range(0, 50);
            (0, 0, onel, zeros)
        }
        _ => {
            let twos = rng.gen_range(0, 50);
            let oneu = rng.gen_range(0, 50);
            let onel = rng.gen_range(0, 50);
            let zeros = rng.gen_range(0, 50);
            (twos, oneu, onel, zeros)
        }
    };
    let _ = t;
    clamp_params(params.0, params.1, params.2, params.3)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (twos, oneu, onel, zeros) = gen_for_mode(&mut rng, mode, t);
        let (twos, oneu, onel, zeros) = clamp_params(twos, oneu, onel, zeros);
        let sum = twos + oneu + onel + zeros;
        if sum < 1 || sum > 100_000 {
            continue;
        }
        let (upper, lower, colsum) = generate_test_case(twos, oneu, onel, zeros);
        print_json(upper, lower, &colsum);
    }
}