use vstd::prelude::*;

verus! {

pub open spec fn count_spec(s: Seq<i32>, v: i32) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_spec(s.drop_last(), v) + if s.last() == v { 1int } else { 0int }
    }
}

pub open spec fn filter_even_spec(s: Seq<i32>, n: int) -> Seq<i32>
    decreases n,
{
    if n <= 0 {
        seq![]
    } else if s[n - 1] % 2 == 0 {
        filter_even_spec(s, n - 1).push(s[n - 1])
    } else {
        filter_even_spec(s, n - 1)
    }
}

// Build a sequence by interleaving even values (at even indices) and odd values (at odd indices).
// For the first 2*k elements: positions 0,2,..,2k-2 are evens[0..k], 1,3,..,2k-1 are odds[0..k].
pub open spec fn built_seq(evens: Seq<i32>, odds: Seq<i32>, k: int) -> Seq<i32>
    decreases k,
{
    if k <= 0 {
        seq![]
    } else {
        built_seq(evens, odds, k - 1).push(evens[k - 1]).push(odds[k - 1])
    }
}

pub proof fn lemma_built_len(evens: Seq<i32>, odds: Seq<i32>, k: int)
    requires k >= 0,
    ensures built_seq(evens, odds, k).len() == 2 * k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_built_len(evens, odds, k - 1);
    }
}

pub proof fn lemma_built_index(evens: Seq<i32>, odds: Seq<i32>, k: int, i: int)
    requires
        k >= 0,
        0 <= i < 2 * k,
    ensures
        built_seq(evens, odds, k).len() == 2 * k,
        i % 2 == 0 ==> built_seq(evens, odds, k)[i] == evens[i / 2],
        i % 2 != 0 ==> built_seq(evens, odds, k)[i] == odds[i / 2],
    decreases k,
{
    lemma_built_len(evens, odds, k);
    if k <= 0 {
    } else {
        lemma_built_len(evens, odds, k - 1);
        if i < 2 * (k - 1) {
            lemma_built_index(evens, odds, k - 1, i);
        } else if i == 2 * k - 2 {
            // position of evens[k-1]
            assert(built_seq(evens, odds, k)[i] == evens[k - 1]);
            assert(i / 2 == k - 1);
        } else {
            // i == 2k - 1
            assert(built_seq(evens, odds, k)[i] == odds[k - 1]);
            assert(i / 2 == k - 1);
        }
    }
}

// Prove that filter_even of built_seq equals evens (up to k).
pub proof fn lemma_filter_even_built(evens: Seq<i32>, odds: Seq<i32>, k: int)
    requires
        k >= 0,
        forall|i: int| 0 <= i < k ==> #[trigger] evens[i] % 2 == 0,
        forall|i: int| 0 <= i < k ==> #[trigger] odds[i] % 2 != 0,
    ensures
        filter_even_spec(built_seq(evens, odds, k), 2 * k).len() == k,
    decreases k,
{
    lemma_built_len(evens, odds, k);
    if k <= 0 {
    } else {
        lemma_filter_even_built(evens, odds, k - 1);
        let s = built_seq(evens, odds, k);
        let s_prev = built_seq(evens, odds, k - 1);
        lemma_built_len(evens, odds, k - 1);
        // s = s_prev.push(evens[k-1]).push(odds[k-1])
        // s has length 2k. s[2k-1] = odds[k-1], odd
        // s[2k-2] = evens[k-1], even
        assert(s[2 * k - 1] == odds[k - 1]);
        assert(s[2 * k - 2] == evens[k - 1]);
        assert(s[2 * k - 1] % 2 != 0);
        assert(s[2 * k - 2] % 2 == 0);

        // filter_even_spec(s, 2k): since s[2k-1] is odd, == filter_even_spec(s, 2k-1)
        // filter_even_spec(s, 2k-1): since s[2k-2] is even, == filter_even_spec(s, 2k-2).push(s[2k-2])
        // filter_even_spec(s, 2k-2) should equal filter_even_spec(s_prev, 2k-2)
        lemma_filter_even_prefix(s, s_prev, 2 * (k - 1));
        assert(filter_even_spec(s, 2 * (k - 1)) == filter_even_spec(s_prev, 2 * (k - 1)));
        assert(filter_even_spec(s, 2 * k - 2).len() == k - 1);
        assert(filter_even_spec(s, 2 * k - 1).len() == k);
        assert(filter_even_spec(s, 2 * k).len() == k);
    }
}

pub proof fn lemma_filter_even_prefix(s: Seq<i32>, s_prev: Seq<i32>, m: int)
    requires
        m >= 0,
        m <= s.len(),
        m <= s_prev.len(),
        forall|i: int| 0 <= i < m ==> s[i] == s_prev[i],
    ensures
        filter_even_spec(s, m) == filter_even_spec(s_prev, m),
    decreases m,
{
    if m <= 0 {
    } else {
        lemma_filter_even_prefix(s, s_prev, m - 1);
        assert(s[m - 1] == s_prev[m - 1]);
    }
}

pub fn generate_test_case(evens: &Vec<i32>, odds: &Vec<i32>) -> (result: Vec<i32>)
    requires
        evens.len() == odds.len(),
        1 <= evens.len() <= 10000,
        forall|i: int| 0 <= i < evens.len() ==> 0 <= #[trigger] evens[i] <= 1000,
        forall|i: int| 0 <= i < evens.len() ==> #[trigger] evens[i] % 2 == 0,
        forall|i: int| 0 <= i < odds.len() ==> 0 <= #[trigger] odds[i] <= 1000,
        forall|i: int| 0 <= i < odds.len() ==> #[trigger] odds[i] % 2 != 0,
    ensures
        2 <= result.len() <= 20000,
        result.len() % 2 == 0,
        result.len() == 2 * evens.len(),
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
        filter_even_spec(result@, result.len() as int).len() == result.len() as int / 2,
{
    let k = evens.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < k
        invariant
            0 <= i <= k,
            k == evens.len(),
            k == odds.len(),
            result.len() == 2 * i,
            result@ == built_seq(evens@, odds@, i as int),
            forall|j: int| 0 <= j < evens.len() ==> 0 <= #[trigger] evens[j] <= 1000,
            forall|j: int| 0 <= j < odds.len() ==> 0 <= #[trigger] odds[j] <= 1000,
            forall|j: int| 0 <= j < evens.len() ==> #[trigger] evens[j] % 2 == 0,
            forall|j: int| 0 <= j < odds.len() ==> #[trigger] odds[j] % 2 != 0,
        decreases k - i,
    {
        result.push(evens[i]);
        result.push(odds[i]);
        i = i + 1;
        proof {
            lemma_built_len(evens@, odds@, i as int);
        }
    }

    proof {
        lemma_built_len(evens@, odds@, k as int);
        assert(result.len() == 2 * k);
        assert forall|j: int| 0 <= j < result.len() implies 0 <= #[trigger] result[j] <= 1000 by {
            lemma_built_index(evens@, odds@, k as int, j);
            if j % 2 == 0 {
                assert(result[j] == evens[j / 2]);
            } else {
                assert(result[j] == odds[j / 2]);
            }
        }
        lemma_filter_even_built(evens@, odds@, k as int);
    }

    result
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_even(rng: &mut Rng) -> i32 {
    let v = rng.gen_usize(0, 500) as i32 * 2;
    v.min(1000)
}

fn make_odd(rng: &mut Rng) -> i32 {
    let v = rng.gen_usize(0, 499) as i32 * 2 + 1;
    v.min(999)
}

fn gen_mode(rng: &mut Rng, mode: usize, k: usize) -> (Vec<i32>, Vec<i32>) {
    let mut evens = Vec::with_capacity(k);
    let mut odds = Vec::with_capacity(k);
    match mode {
        0 => {
            for _ in 0..k {
                evens.push(make_even(rng));
                odds.push(make_odd(rng));
            }
        }
        1 => {
            for _ in 0..k {
                evens.push(0);
                odds.push(1);
            }
        }
        2 => {
            for _ in 0..k {
                evens.push(1000);
                odds.push(999);
            }
        }
        3 => {
            for i in 0..k {
                evens.push(((i * 2) % 1001) as i32 & !1);
                odds.push((((i * 2) % 1000) as i32) | 1);
            }
        }
        4 => {
            for i in 0..k {
                let e = (2 * i) as i32;
                evens.push(if e > 1000 { 1000 } else { e });
                let o = (2 * i + 1) as i32;
                odds.push(if o > 999 { 999 } else { o });
            }
        }
        5 => {
            for i in 0..k {
                let e = (2 * (k - 1 - i)) as i32;
                evens.push(if e > 1000 { 1000 } else { e });
                let o = (2 * (k - 1 - i) + 1) as i32;
                odds.push(if o > 999 { 999 } else { o });
            }
        }
        6 => {
            for _ in 0..k {
                evens.push(2);
                odds.push(3);
            }
        }
        7 => {
            for i in 0..k {
                evens.push(if i % 2 == 0 { 0 } else { 1000 });
                odds.push(if i % 2 == 0 { 1 } else { 999 });
            }
        }
        8 => {
            for _ in 0..k {
                evens.push(make_even(rng));
                odds.push(1);
            }
        }
        9 => {
            for _ in 0..k {
                evens.push(0);
                odds.push(make_odd(rng));
            }
        }
        _ => {
            for _ in 0..k {
                evens.push(make_even(rng));
                odds.push(make_odd(rng));
            }
        }
    }
    (evens, odds)
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let k = match mode {
            0 => 1 + (t % 20),
            1 => 1,
            2 => 2,
            3 => 10,
            4 => 100,
            5 => 1000,
            6 => 10000,
            7 => 5 + (t % 50),
            8 => 50 + (t % 100),
            9 => 500 + (t % 500),
            _ => 1 + (t % 100),
        };
        let k = if k > 10000 { 10000 } else { k };
        let k = if k < 1 { 1 } else { k };
        let (evens, odds) = gen_mode(&mut rng, mode, k);
        let nums = generate_test_case(&evens, &odds);
        print_json(&nums);
    }
}