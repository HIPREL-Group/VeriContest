use vstd::prelude::*;

verus! {

pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occurrences(s.drop_last(), value) + 
            if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

pub proof fn count_push(s: Seq<i32>, v: i32, value: i32)
    ensures
        count_occurrences(s.push(v), value) ==
            count_occurrences(s, value) + (if v == value { 1 as nat } else { 0 as nat }),
{
    let sp = s.push(v);
    assert(sp.len() == s.len() + 1);
    assert(sp.drop_last() == s);
    assert(sp.last() == v);
}

// Build a sequence consisting of `count` pairs: pairs[0], pairs[0], pairs[1], pairs[1], ...
pub open spec fn pair_seq(pairs: Seq<i32>) -> Seq<i32>
    decreases pairs.len()
{
    if pairs.len() == 0 {
        Seq::<i32>::empty()
    } else {
        pair_seq(pairs.drop_last()).push(pairs.last()).push(pairs.last())
    }
}

pub proof fn pair_seq_count(pairs: Seq<i32>, value: i32)
    ensures count_occurrences(pair_seq(pairs), value) % 2 == 0,
    decreases pairs.len(),
{
    if pairs.len() == 0 {
        assert(pair_seq(pairs) =~= Seq::<i32>::empty());
    } else {
        pair_seq_count(pairs.drop_last(), value);
        let ps1 = pair_seq(pairs.drop_last());
        let last = pairs.last();
        let ps2 = ps1.push(last);
        let ps3 = ps2.push(last);
        count_push(ps1, last, value);
        count_push(ps2, last, value);
        assert(pair_seq(pairs) == ps3);
        // count(ps3, value) = count(ps1, value) + 2*(if last==value {1} else {0})
        if last == value {
            assert(count_occurrences(ps3, value) == count_occurrences(ps1, value) + 2);
        } else {
            assert(count_occurrences(ps3, value) == count_occurrences(ps1, value));
        }
    }
}

pub proof fn pair_seq_count_unique(pairs: Seq<i32>, unique: i32)
    requires forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i] != unique,
    ensures count_occurrences(pair_seq(pairs), unique) == 0,
    decreases pairs.len(),
{
    if pairs.len() == 0 {
        assert(pair_seq(pairs) =~= Seq::<i32>::empty());
    } else {
        assert(pairs.last() == pairs[pairs.len() - 1]);
        assert(pairs.last() != unique);
        assert forall|i: int| 0 <= i < pairs.drop_last().len() implies #[trigger] pairs.drop_last()[i] != unique by {
            assert(pairs.drop_last()[i] == pairs[i]);
        }
        pair_seq_count_unique(pairs.drop_last(), unique);
        let ps1 = pair_seq(pairs.drop_last());
        let last = pairs.last();
        let ps2 = ps1.push(last);
        let ps3 = ps2.push(last);
        count_push(ps1, last, unique);
        count_push(ps2, last, unique);
        assert(pair_seq(pairs) == ps3);
    }
}

// The full sequence is pair_seq(pairs).push(unique)
pub open spec fn full_seq(pairs: Seq<i32>, unique: i32) -> Seq<i32> {
    pair_seq(pairs).push(unique)
}

pub proof fn full_seq_count_unique(pairs: Seq<i32>, unique: i32)
    requires forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i] != unique,
    ensures count_occurrences(full_seq(pairs, unique), unique) == 1,
{
    pair_seq_count_unique(pairs, unique);
    count_push(pair_seq(pairs), unique, unique);
}

pub proof fn full_seq_count_other(pairs: Seq<i32>, unique: i32, other: i32)
    requires other != unique,
    ensures count_occurrences(full_seq(pairs, unique), other) % 2 == 0,
{
    pair_seq_count(pairs, other);
    count_push(pair_seq(pairs), unique, other);
    // count = count(pair_seq) + 0 since unique != other
}

pub proof fn pair_seq_len(pairs: Seq<i32>)
    ensures pair_seq(pairs).len() == 2 * pairs.len(),
    decreases pairs.len(),
{
    if pairs.len() == 0 {
    } else {
        pair_seq_len(pairs.drop_last());
    }
}

pub proof fn pair_seq_bounds(pairs: Seq<i32>)
    requires forall|i: int| 0 <= i < pairs.len() ==> -30_000 <= #[trigger] pairs[i] <= 30_000,
    ensures forall|i: int| 0 <= i < pair_seq(pairs).len() ==> -30_000 <= #[trigger] pair_seq(pairs)[i] <= 30_000,
    decreases pairs.len(),
{
    if pairs.len() == 0 {
    } else {
        assert forall|i: int| 0 <= i < pairs.drop_last().len() implies -30_000 <= #[trigger] pairs.drop_last()[i] <= 30_000 by {
            assert(pairs.drop_last()[i] == pairs[i]);
        }
        pair_seq_bounds(pairs.drop_last());
        let ps1 = pair_seq(pairs.drop_last());
        let last = pairs.last();
        assert(pairs.last() == pairs[pairs.len() - 1]);
        assert(-30_000 <= last <= 30_000);
        pair_seq_len(pairs.drop_last());
        pair_seq_len(pairs);
        // pair_seq(pairs) = ps1.push(last).push(last)
        assert forall|i: int| 0 <= i < pair_seq(pairs).len() implies -30_000 <= #[trigger] pair_seq(pairs)[i] <= 30_000 by {
            let ps2 = ps1.push(last);
            let ps3 = ps2.push(last);
            assert(pair_seq(pairs) == ps3);
            if i < ps1.len() {
                assert(ps3[i] == ps1[i]);
            } else if i == ps1.len() {
                assert(ps3[i] == last);
            } else {
                assert(ps3[i] == last);
            }
        }
    }
}

pub fn generate_test_case(
    unique: i32,
    pairs: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        -30_000 <= unique <= 30_000,
        pairs.len() <= 14_999,
        forall|i: int| 0 <= i < pairs.len() ==> -30_000 <= #[trigger] pairs[i] <= 30_000,
        forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i] != unique,
        forall|i: int, j: int| 0 <= i < pairs.len() && 0 <= j < pairs.len() && i != j ==>
            #[trigger] pairs[i] != #[trigger] pairs[j],
    ensures
        1 <= nums.len() <= 30_000,
        forall|i: int| 0 <= i < nums.len() ==> -30_000 <= #[trigger] nums[i] <= 30_000,
        exists|uv: i32| {
            count_occurrences(nums@, uv) == 1 &&
            forall|other: i32| other != uv ==>
                count_occurrences(nums@, other) % 2 == 0
        },
{
    let mut nums: Vec<i32> = Vec::new();
    let n = pairs.len();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == pairs.len(),
            nums.len() == 2 * i,
            nums@ == pair_seq(pairs@.subrange(0, i as int)),
            forall|k: int| 0 <= k < pairs.len() ==> -30_000 <= #[trigger] pairs[k] <= 30_000,
        decreases n - i,
    {
        let v = pairs[i];
        proof {
            let sub_before = pairs@.subrange(0, i as int);
            let sub_after = pairs@.subrange(0, (i + 1) as int);
            assert(sub_after.len() == i + 1);
            assert(sub_after.drop_last() =~= sub_before);
            assert(sub_after.last() == pairs@[i as int]);
            assert(pair_seq(sub_after) == pair_seq(sub_before).push(v).push(v));
        }
        nums.push(v);
        nums.push(v);
        i = i + 1;
    }

    proof {
        assert(pairs@.subrange(0, n as int) =~= pairs@);
        assert(nums@ == pair_seq(pairs@));
        pair_seq_len(pairs@);
        pair_seq_bounds(pairs@);
    }

    nums.push(unique);

    proof {
        assert(nums@ =~= pair_seq(pairs@).push(unique));
        assert(nums@ == full_seq(pairs@, unique));
        full_seq_count_unique(pairs@, unique);
        assert forall|other: i32| other != unique implies count_occurrences(nums@, other) % 2 == 0 by {
            full_seq_count_other(pairs@, unique, other);
        }
        assert(count_occurrences(nums@, unique) == 1);

        let uv = unique;
        assert(count_occurrences(nums@, uv) == 1);
        assert(forall|other: i32| other != uv ==> count_occurrences(nums@, other) % 2 == 0);
    }

    nums
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_distinct_pairs(rng: &mut Rng, unique: i32, count: usize) -> Vec<i32> {
    // Use a seen set over range [-30000, 30000]
    let mut used = vec![false; 60_001];
    used[(unique + 30_000) as usize] = true;
    let mut pairs: Vec<i32> = Vec::with_capacity(count);
    let mut attempts = 0u64;
    while pairs.len() < count {
        attempts += 1;
        let v = rng.gen_range_i32(-30_000, 30_000);
        let idx = (v + 30_000) as usize;
        if !used[idx] {
            used[idx] = true;
            pairs.push(v);
        }
        if attempts > 10_000_000 {
            // Fallback: scan
            for v in -30_000i32..=30_000 {
                let idx = (v + 30_000) as usize;
                if !used[idx] {
                    used[idx] = true;
                    pairs.push(v);
                    if pairs.len() >= count { break; }
                }
            }
            break;
        }
    }
    pairs
}

fn shuffle(rng: &mut Rng, nums: &mut Vec<i32>) {
    let n = nums.len();
    if n <= 1 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        nums.swap(i, j);
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

fn gen_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, Vec<i32>, bool) {
    // returns (unique, pairs, should_shuffle)
    match mode {
        0 => {
            // minimal: just unique
            let u = rng.gen_range_i32(-30_000, 30_000);
            (u, Vec::new(), false)
        }
        1 => {
            // maximum size: 14999 pairs + 1 = 29999
            let u = rng.gen_range_i32(-30_000, 30_000);
            let pairs = build_distinct_pairs(rng, u, 14_999);
            (u, pairs, true)
        }
        2 => {
            // unique = 0
            let count = rng.gen_range_usize(0, 100);
            let pairs = build_distinct_pairs(rng, 0, count);
            (0, pairs, true)
        }
        3 => {
            // unique = 30000 (max)
            let count = rng.gen_range_usize(0, 200);
            let pairs = build_distinct_pairs(rng, 30_000, count);
            (30_000, pairs, true)
        }
        4 => {
            // unique = -30000 (min)
            let count = rng.gen_range_usize(0, 200);
            let pairs = build_distinct_pairs(rng, -30_000, count);
            (-30_000, pairs, true)
        }
        5 => {
            // unique at beginning (no shuffle)
            let u = rng.gen_range_i32(-30_000, 30_000);
            let count = rng.gen_range_usize(1, 50);
            let pairs = build_distinct_pairs(rng, u, count);
            // We build nums as [pairs pairs...] then push unique -> unique at end.
            // To put at beginning we'd need different generator; skip, no shuffle means unique at end.
            (u, pairs, false)
        }
        6 => {
            // small random
            let u = rng.gen_range_i32(-10, 10);
            let count = rng.gen_range_usize(0, 10);
            // pairs in [-30000,30000] excluding u
            let pairs = build_distinct_pairs(rng, u, count);
            (u, pairs, true)
        }
        7 => {
            // medium
            let u = rng.gen_range_i32(-30_000, 30_000);
            let count = rng.gen_range_usize(500, 1500);
            let pairs = build_distinct_pairs(rng, u, count);
            (u, pairs, true)
        }
        8 => {
            // single pair + unique
            let u = rng.gen_range_i32(-30_000, 30_000);
            let pairs = build_distinct_pairs(rng, u, 1);
            (u, pairs, true)
        }
        9 => {
            // size about 14999
            let u = rng.gen_range_i32(-30_000, 30_000);
            let count = rng.gen_range_usize(5000, 14_999);
            let pairs = build_distinct_pairs(rng, u, count);
            (u, pairs, true)
        }
        _ => {
            let u = rng.gen_range_i32(-30_000, 30_000);
            let count = rng.gen_range_usize(0, 500);
            let pairs = build_distinct_pairs(rng, u, count);
            let _ = t;
            (u, pairs, true)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (unique, pairs, shuf) = gen_case(&mut rng, mode, t);
        let mut nums = generate_test_case(unique, &pairs);
        if shuf {
            shuffle(&mut rng, &mut nums);
        }
        print_json(&nums);
    }
}