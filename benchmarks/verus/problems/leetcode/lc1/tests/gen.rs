use vstd::prelude::*;

verus! {

spec fn filler_index(k: int, idx_a: int, idx_b: int) -> int {
    k - (if idx_a < k { 1int } else { 0int })
      - (if idx_b < k { 1int } else { 0int })
}

pub fn generate_test_case(
    a_val: i32,
    b_val: i32,
    idx_a: usize,
    idx_b: usize,
    fillers: &Vec<i32>,
    target: i32,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        a_val as int + b_val as int == target as int,
        -1_000_000_000 <= a_val <= 1_000_000_000,
        -1_000_000_000 <= b_val <= 1_000_000_000,
        -1_000_000_000 <= target <= 1_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==>
            -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
        fillers.len() + 2 >= 2,
        fillers.len() + 2 <= 10_000,
        idx_a < fillers.len() + 2,
        idx_b < fillers.len() + 2,
        idx_a != idx_b,
        forall|i: int, j: int|
            0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                ==> fillers[i] != fillers[j],
        forall|i: int| 0 <= i < fillers.len() ==>
            fillers[i] != a_val && fillers[i] != b_val,
        forall|i: int| 0 <= i < fillers.len() ==> (
            (#[trigger] fillers[i]) as int + a_val as int != target as int
            && fillers[i] as int + b_val as int != target as int
        ),
        forall|i: int, j: int|
            0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                ==> (#[trigger] fillers[i]) as int + (#[trigger] fillers[j]) as int != target as int,
    ensures
        2 <= nums.len() <= 10_000,
        -1_000_000_000 <= target <= 1_000_000_000,
        forall|i: int|
            0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        exists|i: int, j: int|
            0 <= i < nums.len() && 0 <= j < nums.len() && i != j
                && nums[i] + nums[j] == target,
        forall|i1: int, j1: int, i2: int, j2: int|
            0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                && 0 <= i2 < nums.len() && 0 <= j2 < nums.len() && i2 != j2
                && nums[i1] + nums[j1] == target && nums[i2] + nums[j2] == target
                ==> (i1 == i2 && j1 == j2) || (i1 == j2 && j1 == i2),
{
    let n: usize = fillers.len() + 2;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 10_000,
            0 <= pos <= n,
            nums.len() == pos,
            idx_a < n,
            idx_b < n,
            idx_a != idx_b,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx_a < pos { 1usize } else { 0usize })
                      - (if idx_b < pos { 1usize } else { 0usize }),
            forall|k: int| 0 <= k < pos as int && k == idx_a as int ==>
                #[trigger] nums[k] == a_val,
            forall|k: int| 0 <= k < pos as int && k == idx_b as int ==>
                #[trigger] nums[k] == b_val,
            forall|k: int| 0 <= k < pos as int && k != idx_a as int && k != idx_b as int ==>
                #[trigger] nums[k] == fillers[filler_index(k, idx_a as int, idx_b as int)],
            forall|k: int| 0 <= k < pos as int ==>
                -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            a_val as int + b_val as int == target as int,
            -1_000_000_000 <= a_val <= 1_000_000_000,
            -1_000_000_000 <= b_val <= 1_000_000_000,
            -1_000_000_000 <= target <= 1_000_000_000,
            forall|i: int| 0 <= i < fillers.len() ==>
                -1_000_000_000 <= #[trigger] fillers[i] <= 1_000_000_000,
            forall|i: int, j: int|
                0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                    ==> fillers[i] != fillers[j],
            forall|i: int| 0 <= i < fillers.len() ==>
                fillers[i] != a_val && fillers[i] != b_val,
            forall|i: int| 0 <= i < fillers.len() ==> (
                (#[trigger] fillers[i]) as int + a_val as int != target as int
                && fillers[i] as int + b_val as int != target as int
            ),
            forall|i: int, j: int|
                0 <= i < fillers.len() && 0 <= j < fillers.len() && i != j
                    ==> (#[trigger] fillers[i]) as int + (#[trigger] fillers[j]) as int != target as int,
        decreases n - pos,
    {
        if pos == idx_a {
            nums.push(a_val);
        } else if pos == idx_b {
            nums.push(b_val);
        } else {
            assert(fi < fillers.len());
            assert(fi as int == filler_index(pos as int, idx_a as int, idx_b as int));
            nums.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    if mutation_kind == 1u8 {
        nums.set(idx_a, b_val);
        nums.set(idx_b, a_val);
    }

    proof {
        if mutation_kind == 1u8 {
            // Swap case: nums[idx_a] == b_val, nums[idx_b] == a_val,
            // other positions unchanged (fillers).
            assert(nums[idx_a as int] == b_val);
            assert(nums[idx_b as int] == a_val);
            assert(nums[idx_a as int] + nums[idx_b as int] == target);

            assert forall|k: int|
                0 <= k < nums.len()
                implies -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000
            by {}

            assert forall|i1: int, j1: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                    && nums[i1] + nums[j1] == target
                implies
                (i1 == idx_a as int && j1 == idx_b as int)
                    || (i1 == idx_b as int && j1 == idx_a as int)
            by {
                let fi1 = filler_index(i1, idx_a as int, idx_b as int);
                let fj1 = filler_index(j1, idx_a as int, idx_b as int);
                if i1 == idx_a as int {
                    if j1 != idx_b as int {
                        assert(nums[j1] == fillers[fj1]);
                        assert(fillers[fj1] as int + b_val as int != target as int);
                    }
                } else if i1 == idx_b as int {
                    if j1 != idx_a as int {
                        assert(nums[j1] == if j1 == idx_a as int { b_val } else { fillers[fj1] });
                        if j1 == idx_a as int {
                        } else {
                            assert(nums[j1] == fillers[fj1]);
                            assert(fillers[fj1] as int + a_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i1] == fillers[fi1]);
                    if j1 == idx_a as int {
                        assert(fillers[fi1] as int + b_val as int != target as int);
                    } else if j1 == idx_b as int {
                        assert(fillers[fi1] as int + a_val as int != target as int);
                    } else {
                        assert(nums[j1] == fillers[fj1]);
                        if fi1 == fj1 {
                        }
                        assert(fi1 != fj1);
                        assert(fillers[fi1] as int + fillers[fj1] as int != target as int);
                    }
                }
            }
        } else {
            // Standard case: nums[idx_a] == a_val, nums[idx_b] == b_val
            assert(nums[idx_a as int] == a_val);
            assert(nums[idx_b as int] == b_val);
            assert(nums[idx_a as int] + nums[idx_b as int] == target);

            assert forall|i1: int, j1: int|
                0 <= i1 < nums.len() && 0 <= j1 < nums.len() && i1 != j1
                    && nums[i1] + nums[j1] == target
                implies
                (i1 == idx_a as int && j1 == idx_b as int)
                    || (i1 == idx_b as int && j1 == idx_a as int)
            by {
                let fi1 = filler_index(i1, idx_a as int, idx_b as int);
                let fj1 = filler_index(j1, idx_a as int, idx_b as int);
                if i1 == idx_a as int {
                    if j1 != idx_b as int {
                        assert(nums[j1] == fillers[fj1]);
                        assert(fillers[fj1] as int + a_val as int != target as int);
                    }
                } else if i1 == idx_b as int {
                    if j1 != idx_a as int {
                        assert(nums[j1] == if j1 == idx_b as int { b_val } else { fillers[fj1] });
                        if j1 == idx_b as int {
                        } else {
                            assert(nums[j1] == fillers[fj1]);
                            assert(fillers[fj1] as int + b_val as int != target as int);
                        }
                    }
                } else {
                    assert(nums[i1] == fillers[fi1]);
                    if j1 == idx_a as int {
                        assert(fillers[fi1] as int + a_val as int != target as int);
                    } else if j1 == idx_b as int {
                        assert(fillers[fi1] as int + b_val as int != target as int);
                    } else {
                        assert(nums[j1] == fillers[fj1]);
                        if fi1 == fj1 {
                        }
                        assert(fi1 != fj1);
                        assert(fillers[fi1] as int + fillers[fj1] as int != target as int);
                    }
                }
            }
        }
    }

    nums
}

} // verus!

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        self.gen_range_i64(lo as i64, hi as i64) as usize
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

/// Build fillers that satisfy all the preconditions of generate_test_case:
/// - each filler is distinct, in [-1e9, 1e9]
/// - no filler equals a_val or b_val
/// - no filler pairs with a_val, b_val, or another filler to hit target
fn make_fillers(rng: &mut Rng, count: usize, a_val: i64, b_val: i64, target: i64) -> Vec<i32> {
    use std::collections::HashSet;
    let mut used: HashSet<i64> = HashSet::new();
    used.insert(a_val);
    used.insert(b_val);
    let mut fillers: Vec<i32> = Vec::new();
    while fillers.len() < count {
        let v = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
        if used.contains(&v) { continue; }
        let comp = target - v;
        if used.contains(&comp) { continue; }
        if v == comp { continue; }
        // Check no existing filler sums with v to target
        let mut ok = true;
        for f in fillers.iter() {
            if (*f as i64) + v == target { ok = false; break; }
        }
        if !ok { continue; }
        used.insert(v);
        fillers.push(v as i32);
    }
    fillers
}

/// Convenience: pick two distinct positions in [0, n)
fn pick_positions(rng: &mut Rng, n: usize) -> (usize, usize) {
    let idx_a = rng.gen_range_usize(0, n - 1);
    let mut idx_b = rng.gen_range_usize(0, n - 2);
    if idx_b >= idx_a { idx_b += 1; }
    (idx_a, idx_b)
}

/// Emit a test case through the verified constructor
fn emit_case(
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    a_val: i32,
    b_val: i32,
    idx_a: usize,
    idx_b: usize,
    fillers: &Vec<i32>,
    target: i32,
    mutation_kind: u8,
) {
    use std::io::Write;
    let nums = generate_test_case(a_val, b_val, idx_a, idx_b, fillers, target, mutation_kind);
    let key = format!("{:?}|{}", nums, target);
    if seen.insert(key) {
        let result = Solution::two_sum(nums.clone(), target);
        writeln!(out, "{}", json!({"input": {"nums": nums, "target": target}, "output": result})).unwrap();
        *count += 1;
    }
}

/// Build and emit a case from high-level parameters
fn build_and_emit(
    rng: &mut Rng,
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    n: usize,
    a_val: i64,
    b_val: i64,
    idx_a: usize,
    idx_b: usize,
    mutation_kind: u8,
) {
    let target = a_val + b_val;
    let filler_count = n - 2;
    let fillers = make_fillers(rng, filler_count, a_val, b_val, target);
    emit_case(out, seen, count, a_val as i32, b_val as i32, idx_a, idx_b, &fillers, target as i32, mutation_kind);
}

/// Build with random positions
fn build_random_pos(
    rng: &mut Rng,
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    n: usize,
    a_val: i64,
    b_val: i64,
) {
    let (idx_a, idx_b) = pick_positions(rng, n);
    let mutation_kind = rng.gen_range_usize(0, 1) as u8;
    build_and_emit(rng, out, seen, count, n, a_val, b_val, idx_a, idx_b, mutation_kind);
}

fn main() {
    use std::collections::HashSet;
    use std::io::Write;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let goal = 100usize;

    // === LeetCode examples (hand-crafted fillers) ===
    // [2,7,11,15] target=9 => a=2, b=7 at idx 0,1, fillers=[11,15]
    emit_case(&mut out, &mut seen, &mut count, 2, 7, 0, 1, &vec![11, 15], 9, 0);
    // [3,2,4] target=6 => a=2, b=4 at idx 1,2, fillers=[3]
    emit_case(&mut out, &mut seen, &mut count, 2, 4, 1, 2, &vec![3], 6, 0);
    // [3,3] target=6 => a=3, b=3 at idx 0,1, fillers=[]
    emit_case(&mut out, &mut seen, &mut count, 3, 3, 0, 1, &vec![], 6, 0);

    // === Minimal n=2 edge cases ===
    emit_case(&mut out, &mut seen, &mut count, 0, 0, 0, 1, &vec![], 0, 0);
    emit_case(&mut out, &mut seen, &mut count, -1_000_000_000, 1_000_000_000, 0, 1, &vec![], 0, 0);
    emit_case(&mut out, &mut seen, &mut count, 1_000_000_000, -1_000_000_000, 0, 1, &vec![], 0, 1);
    emit_case(&mut out, &mut seen, &mut count, 500_000_000, 500_000_000, 0, 1, &vec![], 1_000_000_000, 0);
    emit_case(&mut out, &mut seen, &mut count, -500_000_000, -500_000_000, 0, 1, &vec![], -1_000_000_000, 1);
    emit_case(&mut out, &mut seen, &mut count, 1, -1, 0, 1, &vec![], 0, 0);
    emit_case(&mut out, &mut seen, &mut count, 0, 1_000_000_000, 0, 1, &vec![], 1_000_000_000, 1);

    // === Boundary targets with fillers ===
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 5, 999_999_999, 1, 0, 4, 0);
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 5, -999_999_999, -1, 0, 4, 1);
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 10, 42, -42, 3, 7, 0);

    // === Position strategies (n=10) ===
    // Both at start
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 10, 100, 200, 0, 1, 0);
    // Both at end
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 10, 100, 200, 8, 9, 1);
    // First and last
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 10, 100, 200, 0, 9, 0);
    // Adjacent in middle
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 10, 100, 200, 4, 5, 1);
    // Far apart
    build_and_emit(&mut rng, &mut out, &mut seen, &mut count, 20, 77, -77, 2, 17, 0);

    // === Value strategies ===
    // Both positive
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 8, 300_000_000, 400_000_000);
    // Both negative
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 8, -300_000_000, -400_000_000);
    // Mixed signs
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 8, -500_000_000, 500_000_000);
    // Near zero
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 12, 1, 2);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 12, -3, 5);
    // Near boundary
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 6, 999_999_990, -999_999_980);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 6, -999_999_995, 999_999_985);
    // One zero
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 10, 0, 42);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 10, 0, -999_999_999);
    // Equal values (a == b)
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 10, 250_000_000, 250_000_000);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 10, -123_456, -123_456);

    // === Target strategies ===
    // target = 0
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, 777, -777);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, 999_999_999, -999_999_999);
    // target near zero
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, 500_000_001, -500_000_000);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, -500_000_002, 500_000_000);
    // target = ±1_000_000_000
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, 700_000_000, 300_000_000);
    build_random_pos(&mut rng, &mut out, &mut seen, &mut count, 15, -700_000_000, -300_000_000);

    // === Filler strategies with specific sizes ===
    // All positive fillers (small n, force positive filler range by using negative answer pair)
    {
        let n = 8;
        let a_val: i64 = -999_000_000;
        let b_val: i64 = -999_000_001;
        let target = a_val + b_val;
        let (idx_a, idx_b) = pick_positions(&mut rng, n);
        // Hand-generate positive fillers
        let mut fillers: Vec<i32> = Vec::new();
        let mut used: std::collections::HashSet<i64> = std::collections::HashSet::new();
        used.insert(a_val); used.insert(b_val);
        while fillers.len() < n - 2 {
            let v = rng.gen_range_i64(1, 999_000_000);
            if used.contains(&v) { continue; }
            let comp = target - v;
            if used.contains(&comp) { continue; }
            if v == comp { continue; }
            let mut ok = true;
            for f in fillers.iter() { if (*f as i64) + v == target { ok = false; break; } }
            if !ok { continue; }
            used.insert(v);
            fillers.push(v as i32);
        }
        emit_case(&mut out, &mut seen, &mut count, a_val as i32, b_val as i32, idx_a, idx_b, &fillers, target as i32, 1);
    }

    // === Tiny random (n=2..5) ===
    for _ in 0..8 {
        if count >= goal { break; }
        let n = rng.gen_range_usize(2, 5);
        let a = rng.gen_range_i64(-500_000_000, 500_000_000);
        let b = rng.gen_range_i64(
            (-1_000_000_000i64).max(-1_000_000_000 - a),
            1_000_000_000i64.min(1_000_000_000 - a),
        );
        build_random_pos(&mut rng, &mut out, &mut seen, &mut count, n, a, b);
    }

    // === Small random (n=6..20) ===
    for _ in 0..12 {
        if count >= goal { break; }
        let n = rng.gen_range_usize(6, 20);
        let a = rng.gen_range_i64(-500_000_000, 500_000_000);
        let b = rng.gen_range_i64(
            (-1_000_000_000i64).max(-1_000_000_000 - a),
            1_000_000_000i64.min(1_000_000_000 - a),
        );
        build_random_pos(&mut rng, &mut out, &mut seen, &mut count, n, a, b);
    }

    // === Medium random (n=21..200) ===
    for _ in 0..15 {
        if count >= goal { break; }
        let n = rng.gen_range_usize(21, 200);
        let a = rng.gen_range_i64(-500_000_000, 500_000_000);
        let b = rng.gen_range_i64(
            (-1_000_000_000i64).max(-1_000_000_000 - a),
            1_000_000_000i64.min(1_000_000_000 - a),
        );
        build_random_pos(&mut rng, &mut out, &mut seen, &mut count, n, a, b);
    }

    // === Large random (n=201..2000) ===
    for _ in 0..12 {
        if count >= goal { break; }
        let n = rng.gen_range_usize(201, 2000);
        let a = rng.gen_range_i64(-500_000_000, 500_000_000);
        let b = rng.gen_range_i64(
            (-1_000_000_000i64).max(-1_000_000_000 - a),
            1_000_000_000i64.min(1_000_000_000 - a),
        );
        build_random_pos(&mut rng, &mut out, &mut seen, &mut count, n, a, b);
    }

    // === Fill remaining with diverse random ===
    while count < goal {
        let size_class = rng.gen_range_usize(0, 4);
        let n = match size_class {
            0 => 2,
            1 => rng.gen_range_usize(3, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 200),
            _ => rng.gen_range_usize(201, 2000),
        };
        let strat = rng.gen_range_usize(0, 5);
        let (a, b) = match strat {
            0 => { // both positive
                let a = rng.gen_range_i64(1, 500_000_000);
                let b = rng.gen_range_i64(1, 500_000_000);
                (a, b)
            },
            1 => { // both negative
                let a = rng.gen_range_i64(-500_000_000, -1);
                let b = rng.gen_range_i64(-500_000_000, -1);
                (a, b)
            },
            2 => { // target = 0
                let a = rng.gen_range_i64(-500_000_000, 500_000_000);
                (a, -a)
            },
            3 => { // near boundary
                let a = rng.gen_range_i64(900_000_000, 1_000_000_000);
                let b = rng.gen_range_i64(-1_000_000_000, -900_000_000);
                (a, b)
            },
            4 => { // equal values
                let a = rng.gen_range_i64(-500_000_000, 500_000_000);
                (a, a)
            },
            _ => {
                let a = rng.gen_range_i64(-500_000_000, 500_000_000);
                let b = rng.gen_range_i64(-500_000_000, 500_000_000);
                (a, b)
            },
        };
        build_random_pos(&mut rng, &mut out, &mut seen, &mut count, n, a, b);
    }
}
