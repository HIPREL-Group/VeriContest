use vstd::prelude::*;

verus! {

pub open spec fn seq_contains_id(s: Seq<i32>, id: i32) -> bool {
    exists|k: int| 0 <= k < s.len() && #[trigger] s[k] == id
}

pub open spec fn all_distinct(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

pub open spec fn all_in_range(s: Seq<i32>, n: i32) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= n
}

pub open spec fn friends_strict_incr(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

/// Build order: order[i] = perm_indices[i] + 1, where perm_indices is
/// a permutation of 0..n. Then friends are built from indices too.
pub fn generate_test_case(
    n: usize,
    perm: Vec<i32>,   // a permutation of 1..=n, length n
    friend_ids: Vec<i32>, // strictly increasing subset of 1..=n, len 1..=8
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100,
        perm.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] perm[i] <= n as i32,
        forall|i: int, j: int| 0 <= i < j < n as int ==> perm[i] != perm[j],
        forall|id: i32| 1 <= id <= n as i32 ==> seq_contains_id(perm@, id),
        1 <= friend_ids.len() <= 8,
        friend_ids.len() <= n,
        forall|i: int| 0 <= i < friend_ids.len() ==> 1 <= #[trigger] friend_ids[i] <= n as i32,
        forall|i: int, j: int| 0 <= i < j < friend_ids.len() ==> friend_ids[i] < friend_ids[j],
        forall|i: int| 0 <= i < friend_ids.len() ==> seq_contains_id(perm@, #[trigger] friend_ids[i]),
    ensures
        ({
            let order = result.0;
            let friends = result.1;
            &&& 1 <= order.len() <= 100
            &&& (forall|i: int| 0 <= i < order.len() ==> 1 <= #[trigger] order[i] <= order.len() as i32)
            &&& (forall|i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j])
            &&& (forall|id: int| 1 <= id <= order.len() ==> #[trigger] order@.contains(id as i32))
            &&& 1 <= friends.len() <= 8
            &&& friends.len() <= order.len()
            &&& (forall|i: int| 0 <= i < friends.len() ==> 1 <= #[trigger] friends[i] <= order.len() as i32)
            &&& (forall|i: int, j: int| 0 <= i < j < friends.len() ==> friends[i] < friends[j])
            &&& (forall|i: int| 0 <= i < friends.len() ==> order@.contains(#[trigger] friends[i]))
        }),
{
    let order = perm;
    let friends = friend_ids;

    proof {
        assert(order.len() == n);
        assert forall|id: int| 1 <= id <= order.len() implies #[trigger] order@.contains(id as i32) by {
            assert(1 <= id as i32 <= n as i32);
            assert(seq_contains_id(order@, id as i32));
            let k = choose|k: int| 0 <= k < order@.len() && #[trigger] order@[k] == id as i32;
            assert(order@[k] == id as i32);
        }
        assert forall|i: int| 0 <= i < friends.len() implies order@.contains(#[trigger] friends[i]) by {
            assert(seq_contains_id(order@, friends[i]));
            let k = choose|k: int| 0 <= k < order@.len() && #[trigger] order@[k] == friends[i];
            assert(order@[k] == friends[i]);
        }
    }

    (order, friends)
}

} // verus!

// ===== Unverified Rust below =====

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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn shuffle(v: &mut Vec<i32>, rng: &mut Rng) {
    let n = v.len();
    if n <= 1 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range(0, i);
        v.swap(i, j);
    }
}

fn gen_perm(n: usize, rng: &mut Rng, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    match mode {
        0 => { /* identity */ }
        1 => { v.reverse(); }
        2 => {
            // rotate by 1
            if n > 1 {
                let last = v.pop().unwrap();
                v.insert(0, last);
            }
        }
        _ => { shuffle(&mut v, rng); }
    }
    v
}

fn gen_friends(n: usize, rng: &mut Rng, mode: usize) -> Vec<i32> {
    let max_k = std::cmp::min(8, n);
    let k = match mode {
        0 => 1,
        1 => max_k,
        2 => std::cmp::min(max_k, (n + 1) / 2),
        _ => rng.gen_range(1, max_k),
    };
    // pick k distinct values from 1..=n
    let mut all: Vec<i32> = (1..=n as i32).collect();
    shuffle(&mut all, rng);
    let mut sel: Vec<i32> = all.into_iter().take(k).collect();
    sel.sort();
    sel
}

fn print_json(order: &[i32], friends: &[i32]) {
    print!("{{\"order\":[");
    for i in 0..order.len() {
        if i > 0 { print!(","); }
        print!("{}", order[i]);
    }
    print!("],\"friends\":[");
    for i in 0..friends.len() {
        if i > 0 { print!(","); }
        print!("{}", friends[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let n = match t % 10 {
            0 => 1,
            1 => 2,
            2 => 8,
            3 => 100,
            4 => 99,
            5 => 50,
            6 => 3,
            7 => 4,
            8 => 16,
            _ => rng.gen_range(1, 100),
        };
        let perm_mode = t % 5;
        let friend_mode = t % 4;

        let perm = gen_perm(n, &mut rng, perm_mode);
        let friends = gen_friends(n, &mut rng, friend_mode);

        let (order, friends) = generate_test_case(n, perm, friends);
        print_json(&order, &friends);
    }
}