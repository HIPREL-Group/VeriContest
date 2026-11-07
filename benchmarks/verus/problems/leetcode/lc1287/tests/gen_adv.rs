use vstd::prelude::*;

verus! {

pub open spec fn count_spec(s: Seq<i32>, v: i32) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == v { 1int } else { 0int }) + count_spec(s.subrange(1, s.len() as int), v)
    }
}

// Lemma: if all elements of s equal v, count_spec(s, v) == s.len()
pub proof fn lemma_count_all_equal(s: Seq<i32>, v: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == v,
    ensures
        count_spec(s, v) == s.len() as int,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies tail[i] == v by {
            assert(tail[i] == s[i + 1]);
        }
        lemma_count_all_equal(tail, v);
    }
}

// Lemma: if all elements of s differ from v, count_spec(s, v) == 0
pub proof fn lemma_count_none_equal(s: Seq<i32>, v: i32)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
    ensures
        count_spec(s, v) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies tail[i] != v by {
            assert(tail[i] == s[i + 1]);
        }
        lemma_count_none_equal(tail, v);
    }
}

// For a sequence built as [all v's], count_spec == len, and for any other v2, count is 0.
pub fn generate_test_case(n: usize, v: i32) -> (arr: Vec<i32>)
    requires
        1 <= n <= 10_000,
        0 <= v <= 100_000,
    ensures
        1 <= arr.len() <= 10_000,
        arr.len() == n,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
        exists|v2: i32| #[trigger] count_spec(arr@, v2) > arr.len() as int / 4,
        forall|v1: i32, v2: i32| (count_spec(arr@, v1) > arr.len() as int / 4
            && count_spec(arr@, v2) > arr.len() as int / 4) ==> v1 == v2,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            arr.len() == i,
            0 <= v <= 100_000,
            forall|k: int| 0 <= k < arr.len() ==> arr[k] == v,
        decreases n - i,
    {
        arr.push(v);
        i = i + 1;
    }

    proof {
        assert(arr.len() == n);
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] == v);
        lemma_count_all_equal(arr@, v);
        assert(count_spec(arr@, v) == arr.len() as int);
        assert(arr.len() as int > arr.len() as int / 4);
        assert(count_spec(arr@, v) > arr.len() as int / 4);

        // Uniqueness: any v2 != v has count 0
        assert forall|v1: i32, v2: i32| (#[trigger] count_spec(arr@, v1) > arr.len() as int / 4
            && #[trigger] count_spec(arr@, v2) > arr.len() as int / 4) implies v1 == v2 by {
            if v1 != v {
                assert forall|k: int| 0 <= k < arr@.len() implies arr@[k] != v1 by {
                    assert(arr@[k] == v);
                }
                lemma_count_none_equal(arr@, v1);
                assert(count_spec(arr@, v1) == 0);
            }
            if v2 != v {
                assert forall|k: int| 0 <= k < arr@.len() implies arr@[k] != v2 by {
                    assert(arr@[k] == v);
                }
                lemma_count_none_equal(arr@, v2);
                assert(count_spec(arr@, v2) == 0);
            }
        }
    }

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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let (n, v) = match mode {
            0 => (1usize, 0i32),
            1 => (1, 100_000),
            2 => (2, rng.gen_range_i32(0, 100_000)),
            3 => (10_000, 0),
            4 => (10_000, 100_000),
            5 => (10_000, rng.gen_range_i32(0, 100_000)),
            6 => (rng.gen_range_usize(1, 20), rng.gen_range_i32(0, 100_000)),
            7 => (rng.gen_range_usize(1, 100), 0),
            8 => (rng.gen_range_usize(1, 100), 100_000),
            9 => (rng.gen_range_usize(100, 1000), rng.gen_range_i32(0, 100_000)),
            _ => (rng.gen_range_usize(1, 10_000), rng.gen_range_i32(0, 100_000)),
        };

        let arr = generate_test_case(n, v);
        print_json(&arr);
    }
}