use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    rounds_raw: &Vec<i32>,
) -> (result: (i32, Vec<i32>))
    requires
        2 <= n <= 100,
        rounds_raw.len() >= 2,
        rounds_raw.len() <= 101,
        forall |i: int| 0 <= i < rounds_raw.len() ==> 1 <= #[trigger] rounds_raw[i] <= n,
        forall |i: int| 0 <= i < rounds_raw.len() - 1 ==> (#[trigger] rounds_raw[i]) != rounds_raw[i + 1],
    ensures
        2 <= result.0 <= 100,
        result.1.len() >= 2,
        result.1.len() <= 101,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0,
        forall |i: int| 0 <= i < result.1.len() - 1 ==> (#[trigger] result.1[i]) != result.1[i + 1],
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < rounds_raw.len()
        invariant
            0 <= i <= rounds_raw.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> out[k] == rounds_raw[k],
        decreases rounds_raw.len() - i,
    {
        out.push(rounds_raw[i]);
        i = i + 1;
    }

    assert(out.len() == rounds_raw.len());
    assert forall |k: int| 0 <= k < out.len() implies 1 <= #[trigger] out[k] <= n by {
        assert(out[k] == rounds_raw[k]);
    }
    assert forall |k: int| 0 <= k < out.len() - 1 implies (#[trigger] out[k]) != out[k + 1] by {
        assert(out[k] == rounds_raw[k]);
        assert(out[k + 1] == rounds_raw[k + 1]);
    }

    (n, out)
}

}

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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_rounds(rng: &mut Rng, n: i32, m_plus_1: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(m_plus_1);
    let first = rng.gen_range_i32(1, n);
    v.push(first);
    while v.len() < m_plus_1 {
        let prev = *v.last().unwrap();
        let mut x = rng.gen_range_i32(1, n - 1);
        if x >= prev {
            x += 1;
        }
        v.push(x);
    }
    v
}

fn print_case(n: i32, rounds: &[i32]) {
    print!("{{\"n\":{},\"rounds\":[", n);
    for i in 0..rounds.len() {
        if i > 0 { print!(","); }
        print!("{}", rounds[i]);
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
        let mode = t % 10;
        let (n, len) = match mode {
            0 => (2i32, 2usize),
            1 => (2i32, 101usize),
            2 => (100i32, 2usize),
            3 => (100i32, 101usize),
            4 => (rng.gen_range_i32(2, 10), rng.gen_range_usize(2, 10)),
            5 => (rng.gen_range_i32(2, 100), rng.gen_range_usize(2, 101)),
            6 => {
                let n = rng.gen_range_i32(2, 100);
                (n, 3usize)
            }
            7 => {
                let n = rng.gen_range_i32(50, 100);
                (n, 101usize)
            }
            8 => (3i32, rng.gen_range_usize(2, 101)),
            9 => (rng.gen_range_i32(2, 100), 2usize),
            _ => (rng.gen_range_i32(2, 100), rng.gen_range_usize(2, 101)),
        };

        let rounds = build_rounds(&mut rng, n, len);

        let (out_n, out_rounds) = generate_test_case(n, &rounds);
        print_case(out_n, &out_rounds[..]);
    }
}