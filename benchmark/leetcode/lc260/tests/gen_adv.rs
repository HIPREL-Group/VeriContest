use vstd::prelude::*;

verus! {

pub open spec fn count_occ(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occ(s.drop_last(), value)
            + if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

pub proof fn count_occ_push(s: Seq<i32>, v: i32, x: i32)
    ensures
        count_occ(s.push(v), x) == count_occ(s, x) + (if v == x { 1 as nat } else { 0 as nat })
{
    let s2 = s.push(v);
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() =~= s);
    assert(s2.last() == v);
}

pub fn generate_test_case(
    a_val: i32,
    b_val: i32,
    pairs: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        a_val != b_val,
        -2_147_483_648 <= a_val <= 2_147_483_647,
        -2_147_483_648 <= b_val <= 2_147_483_647,
        pairs.len() <= 14_999,
        2 + 2 * pairs.len() <= 30_000,
        forall|i: int| 0 <= i < pairs.len() ==>
            -2_147_483_648 <= #[trigger] pairs[i] <= 2_147_483_647,
        forall|i: int| 0 <= i < pairs.len() ==>
            #[trigger] pairs[i] != a_val && pairs[i] != b_val,
        forall|i: int, j: int| 0 <= i < pairs.len() && 0 <= j < pairs.len() && i != j ==>
            #[trigger] pairs[i] != #[trigger] pairs[j],
    ensures
        2 <= nums.len() <= 30_000,
        forall|i: int| 0 <= i < nums.len() ==> -2_147_483_648 <= #[trigger] nums[i] <= 2_147_483_647,
        exists |a: i32, b: i32| {
            a != b
            && count_occ(nums@, a) == 1
            && count_occ(nums@, b) == 1
            && forall |x: i32| x != a && x != b ==> count_occ(nums@, x) == 0 || count_occ(nums@, x) == 2
        },
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(a_val);
    nums.push(b_val);

    proof {
        let s0: Seq<i32> = Seq::empty();
        let s1 = s0.push(a_val);
        let s2 = s1.push(b_val);
        count_occ_push(s0, a_val, a_val);
        count_occ_push(s1, b_val, a_val);
        count_occ_push(s0, a_val, b_val);
        count_occ_push(s1, b_val, b_val);
        assert(nums@ =~= s2);
        assert(a_val != b_val);
        assert(count_occ(nums@, a_val) == 1);
        assert(count_occ(nums@, b_val) == 1);
        assert forall |x: i32| x != a_val && x != b_val implies
            #[trigger] count_occ(nums@, x) == 0 || count_occ(nums@, x) == 2
        by {
            count_occ_push(s0, a_val, x);
            count_occ_push(s1, b_val, x);
            assert(count_occ(nums@, x) == 0);
        }
    }

    nums
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn make_pairs(rng: &mut Rng, count: usize, a: i32, b: i32) -> Vec<i32> {
    use std::collections::HashSet;
    let mut seen: HashSet<i32> = HashSet::new();
    seen.insert(a);
    seen.insert(b);
    let mut res: Vec<i32> = Vec::with_capacity(count);
    while res.len() < count {
        let v = rng.gen_range_i64(-2_147_483_648, 2_147_483_647) as i32;
        if !seen.contains(&v) {
            seen.insert(v);
            res.push(v);
        }
    }
    res
}

fn pick_pair(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 2),
        1 => (-1, 0),
        2 => (0, 1),
        3 => (i32::MIN, i32::MAX),
        4 => (i32::MIN, 0),
        5 => (0, i32::MAX),
        6 => (-1, 1),
        7 => {
            let a = rng.gen_range_i64(-100, 100) as i32;
            let mut b = rng.gen_range_i64(-100, 100) as i32;
            if b == a { b = a.wrapping_add(1); }
            (a, b)
        }
        8 => {
            let a = rng.gen_range_i64(-2_147_483_648, 2_147_483_647) as i32;
            let mut b = rng.gen_range_i64(-2_147_483_648, 2_147_483_647) as i32;
            if b == a { b = a.wrapping_add(1); }
            (a, b)
        }
        9 => (i32::MAX - 1, i32::MAX),
        _ => (i32::MIN, i32::MIN + 1),
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let pair_count: usize = match mode {
            0 => 0,
            1 => 0,
            2 => 1,
            3 => (t % 50) + 1,
            4 => (t % 100),
            5 => 14_999,
            6 => 500,
            7 => (t * 7) % 200,
            8 => (t * 13) % 1000,
            9 => 1,
            _ => (t % 30),
        };
        let pair_count = if pair_count > 14_999 { 14_999 } else { pair_count };

        let (a, b) = pick_pair(&mut rng, mode);
        if a == b { continue; }
        let pairs = make_pairs(&mut rng, pair_count, a, b);
        let nums = generate_test_case(a, b, &pairs);
        print_json(&nums);
    }
}
