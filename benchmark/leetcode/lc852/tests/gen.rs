use vstd::prelude::*;

verus! {

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


pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
    s.len() >= 3
    && 0 < peak < s.len() - 1
    && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
    && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
}

pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

proof fn lemma_sum_deltas_nonneg(deltas: Seq<i32>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

pub fn generate_candidate(
    up_deltas: &Vec<i32>,
    down_deltas: &Vec<i32>,
    base: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        up_deltas.len() >= 1,
        down_deltas.len() >= 1,
        up_deltas.len() + down_deltas.len() + 1 >= 3,
        up_deltas.len() + down_deltas.len() + 1 <= 100_000,
        0 <= base,
        forall|i: int| 0 <= i < up_deltas.len() ==> 1 <= #[trigger] up_deltas[i],
        forall|i: int| 0 <= i < down_deltas.len() ==> 1 <= #[trigger] down_deltas[i],
        base as int + sum_deltas(up_deltas@, up_deltas.len() as int) <= 1_000_000,
        base as int + sum_deltas(up_deltas@, up_deltas.len() as int)
            - sum_deltas(down_deltas@, down_deltas.len() as int) >= 0,
    ensures
        3 <= result.len() <= 100_000,
        forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000,
        exists |peak: int| is_mountain(result@, peak),
{
    // ---- Mutation 1: minimal 3-element mountain [0, peak_val, 0] ----
    if mutation_kind == 1 {
        proof {
            // sum_deltas(up_deltas@, 1) == up_deltas[0]
            // sum_deltas(up_deltas@, 1) <= sum_deltas(up_deltas@, len)
            lemma_sum_deltas_mono(up_deltas@, 1, up_deltas.len() as int);
            assert(sum_deltas(up_deltas@, 0) == 0);
            assert(sum_deltas(up_deltas@, 1) == sum_deltas(up_deltas@, 0) + up_deltas@[0] as int);
            assert(up_deltas[0] as int == sum_deltas(up_deltas@, 1));
            assert(base as int + up_deltas[0] as int
                <= base as int + sum_deltas(up_deltas@, up_deltas.len() as int));
            assert(base as int + up_deltas[0] as int <= 1_000_000);
        }
        let peak_val = base + up_deltas[0];
        proof {
            assert(0 <= peak_val <= 1_000_000);
            assert(peak_val >= 1);
        }
        let mut arr: Vec<i32> = Vec::new();
        arr.push(0i32);
        arr.push(peak_val);
        arr.push(0i32);
        proof {
            assert(arr@.len() == 3);
            assert(arr[0] == 0);
            assert(arr[1] == peak_val);
            assert(arr[2] == 0);
            assert(0 < 1int < arr@.len() - 1);
            assert(arr[0] < arr[1]);
            assert(arr[1] > arr[2]);
            assert forall |a: int, b: int| 0 <= a < b <= 1 implies arr@[a] < arr@[b] by {};
            assert forall |a: int, b: int| 1 <= a < b < 3int implies arr@[a] > arr@[b] by {};
            assert(is_mountain(arr@, 1int));
        }
        return arr;
    }

    let peak_pos: usize = up_deltas.len();

    // ---- Build ascending part ----
    let mut arr: Vec<i32> = Vec::new();

    proof {
        // base <= 1_000_000 because sum_deltas >= 1 and base + sum <= 1_000_000
        lemma_sum_deltas_strict(up_deltas@, 0, up_deltas.len() as int);
        assert(sum_deltas(up_deltas@, up_deltas.len() as int) >= up_deltas.len() as int);
        assert(base as int <= 1_000_000 - up_deltas.len() as int);
        assert(base <= 1_000_000);
    }

    arr.push(base);

    let mut i: usize = 0;
    while i < up_deltas.len()
        invariant
            0 <= i <= up_deltas.len(),
            arr.len() == i + 1,
            peak_pos == up_deltas.len(),
            forall|k: int| 0 <= k <= i as int ==>
                (#[trigger] arr[k]) as int == base as int + sum_deltas(up_deltas@, k),
            forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 1_000_000,
            forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l],
            forall|j: int| 0 <= j < up_deltas.len() ==> #[trigger] up_deltas[j] >= 1i32,
            base as int + sum_deltas(up_deltas@, up_deltas.len() as int) <= 1_000_000,
            0 <= base,
        decreases up_deltas.len() - i,
    {
        let ghost old_len = arr.len();

        proof {
            lemma_sum_deltas_mono(up_deltas@, (i + 1) as int, up_deltas.len() as int);
        }

        let next = arr[i] + up_deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(up_deltas@, (i + 1) as int));
            assert(0 <= next <= 1_000_000) by {
                assert(next as int <= base as int + sum_deltas(up_deltas@, up_deltas.len() as int));
                lemma_sum_deltas_nonneg(up_deltas@, (i + 1) as int);
            };

            assert forall|k: int| 0 <= k < arr.len() implies arr[k] < next by {
                assert(arr[k] as int == base as int + sum_deltas(up_deltas@, k));
                assert(next as int == base as int + sum_deltas(up_deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(up_deltas@, k, (i + 1) as int);
            };
        }

        arr.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr[k] < arr[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(arr[l] == next);
                }
            };
        }
    }

    // arr[0..=peak_pos] is now the ascending part
    let peak_val: i32 = arr[peak_pos];

    proof {
        assert(peak_val as int == base as int + sum_deltas(up_deltas@, up_deltas.len() as int));
    }

    // ---- Build descending part ----
    let mut j: usize = 0;
    while j < down_deltas.len()
        invariant
            0 <= j <= down_deltas.len(),
            arr.len() == peak_pos + 1 + j,
            peak_pos == up_deltas.len(),
            // ascending part preserved
            forall|k: int| 0 <= k <= peak_pos as int ==>
                (#[trigger] arr[k]) as int == base as int + sum_deltas(up_deltas@, k),
            forall|k: int, l: int| 0 <= k < l <= peak_pos as int ==> arr[k] < arr[l],
            // descending part values
            peak_val as int == base as int + sum_deltas(up_deltas@, up_deltas.len() as int),
            forall|k: int| 1 <= k <= j as int ==>
                (#[trigger] arr[peak_pos as int + k]) as int
                    == peak_val as int - sum_deltas(down_deltas@, k),
            // strictly decreasing from peak onward
            forall|k: int, l: int| peak_pos as int <= k < l < arr.len() ==> arr[k] > arr[l],
            // all values in range
            forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 1_000_000,
            // construction params carried
            forall|jj: int| 0 <= jj < down_deltas.len() ==> #[trigger] down_deltas[jj] >= 1i32,
            forall|jj: int| 0 <= jj < up_deltas.len() ==> #[trigger] up_deltas[jj] >= 1i32,
            base as int + sum_deltas(up_deltas@, up_deltas.len() as int)
                - sum_deltas(down_deltas@, down_deltas.len() as int) >= 0,
            base as int + sum_deltas(up_deltas@, up_deltas.len() as int) <= 1_000_000,
            0 <= base,
            up_deltas.len() + down_deltas.len() + 1 <= 100_000,
        decreases down_deltas.len() - j,
    {
        let ghost old_len = arr.len();

        let prev = arr[arr.len() - 1];

        proof {
            // Connect prev to known values
            if j == 0 {
                assert(arr.len() == peak_pos + 1);
                assert(arr.len() - 1 == peak_pos);
                assert(prev as int == base as int + sum_deltas(up_deltas@, peak_pos as int));
                assert(prev == peak_val);
            } else {
                assert(arr.len() - 1 == peak_pos + j);
                assert(prev as int == peak_val as int - sum_deltas(down_deltas@, j as int));
            }

            // Prove prev - down_deltas[j] won't underflow
            // next_val = peak_val - sum_deltas(down_deltas, j+1)
            // sum_deltas(down_deltas, j+1) <= sum_deltas(down_deltas, len)
            // peak_val - sum_deltas(down_deltas, len) >= 0 (from requires)
            lemma_sum_deltas_mono(down_deltas@, (j + 1) as int, down_deltas.len() as int);
            if j == 0 {
                assert(prev as int - down_deltas[j as int] as int
                    == peak_val as int - down_deltas[0] as int);
                assert(sum_deltas(down_deltas@, 0) == 0);
                assert(sum_deltas(down_deltas@, 1) == sum_deltas(down_deltas@, 0) + down_deltas@[0] as int);
                assert(down_deltas[0] as int == sum_deltas(down_deltas@, 1));
                assert(prev as int - down_deltas[j as int] as int
                    >= peak_val as int - sum_deltas(down_deltas@, down_deltas.len() as int));
            } else {
                assert(prev as int - down_deltas[j as int] as int
                    == peak_val as int - sum_deltas(down_deltas@, (j + 1) as int));
                assert(prev as int - down_deltas[j as int] as int
                    >= peak_val as int - sum_deltas(down_deltas@, down_deltas.len() as int));
            }
            assert(prev as int - down_deltas[j as int] as int >= 0);
            // Also <= 1_000_000 since prev <= 1_000_000
            assert(prev as int - down_deltas[j as int] as int <= prev as int);
            assert(prev as int <= 1_000_000);
        }

        let next = prev - down_deltas[j];

        proof {
            // Establish next's value via sum_deltas
            if j == 0 {
                assert(next as int == peak_val as int - down_deltas[0] as int);
                assert(sum_deltas(down_deltas@, 0) == 0);
                assert(sum_deltas(down_deltas@, 1) == sum_deltas(down_deltas@, 0) + down_deltas@[0] as int);
                assert(down_deltas[0] as int == sum_deltas(down_deltas@, 1));
                assert(next as int == peak_val as int - sum_deltas(down_deltas@, 1));
            } else {
                assert(next as int == peak_val as int - sum_deltas(down_deltas@, j as int)
                    - down_deltas[j as int] as int);
                assert(next as int == peak_val as int - sum_deltas(down_deltas@, (j + 1) as int));
            }

            // next >= 0
            lemma_sum_deltas_mono(down_deltas@, (j + 1) as int, down_deltas.len() as int);
            assert(next as int >= peak_val as int
                - sum_deltas(down_deltas@, down_deltas.len() as int));
            assert(next as int >= 0);

            // next <= 1_000_000
            lemma_sum_deltas_nonneg(down_deltas@, (j + 1) as int);
            assert(next as int <= peak_val as int);
            assert(next as int <= 1_000_000);

            // next < prev
            assert(down_deltas[j as int] >= 1i32);
            assert(next < prev);

            // all elements from peak onward are > next
            assert forall|k: int| peak_pos as int <= k < arr.len() implies arr[k] > next by {
                if k == (arr.len() - 1) as int {
                    assert(arr[k] == prev);
                    assert(prev > next);
                } else {
                    // arr[k] > arr[arr.len()-1] by descending invariant, and prev > next
                    assert(arr[k] > prev);
                    assert(prev > next);
                }
            };
        }

        arr.push(next);
        j = j + 1;

        proof {
            assert forall|k: int, l: int| peak_pos as int <= k < l < arr.len()
                implies arr[k] > arr[l] by
            {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(arr[l] == next);
                }
            };

            // Ascending part invariant is preserved (only appended)
            assert forall|k: int, l: int| 0 <= k < l <= peak_pos as int
                implies arr[k] < arr[l] by {};
        }
    }

    // ---- Prove is_mountain ----
    proof {
        let peak = peak_pos as int;
        assert(arr@.len() == (up_deltas.len() + 1 + down_deltas.len()) as int);
        assert(arr@.len() >= 3);
        assert(0 < peak);
        assert(peak < arr@.len() - 1);

        assert forall |a: int, b: int| 0 <= a < b <= peak implies arr@[a] < arr@[b] by {};
        assert forall |a: int, b: int| peak <= a < b < arr@.len() implies arr@[a] > arr@[b] by {};

        assert(is_mountain(arr@, peak));
    }

    arr
}

} // verus!

// ---- Unverified runtime: PRNG, main, JSONL output ----

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i64(1, max_d as i64) as i32).collect()
}

fn make_test(
    up_deltas: Vec<i32>,
    down_deltas: Vec<i32>,
    base: i32,
    mutation_kind: u8,
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    goal: usize,
) {
    if *count >= goal { return; }
    let arr = generate_candidate(&up_deltas, &down_deltas, base, mutation_kind);
    let peak = arr.iter().enumerate().max_by_key(|(_, v)| *v).map(|(i, _)| i).unwrap_or(1);
    let arr = generate_test_case(arr, peak);
    let result = Solution::peak_index_in_mountain_array(arr.clone());
    let line = json!({
        "input": {"arr": arr},
        "output": result
    }).to_string();
    if seen.insert(line.clone()) {
        use std::io::Write;
        writeln!(out, "{}", line).unwrap();
        *count += 1;
    }
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(852);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // ---- Example test cases from description.md ----
    // [0,1,0] peak=1
    make_test(vec![1], vec![1], 0, 0, &mut out, &mut seen, &mut count, goal);
    // [0,2,1,0] peak=1
    make_test(vec![2], vec![1, 1], 0, 0, &mut out, &mut seen, &mut count, goal);
    // [0,10,5,2] peak=1
    make_test(vec![10], vec![5, 3], 0, 0, &mut out, &mut seen, &mut count, goal);

    // ---- Minimal mountains (mutation_kind=1) with various bases ----
    for b in [1i32, 2, 10, 100, 1000, 999_999] {
        make_test(vec![1], vec![1], b, 1, &mut out, &mut seen, &mut count, goal);
    }

    // ---- Tiny arrays (3-5 elements), all-1 deltas, varied peak positions ----
    for n_up in 1usize..=3 {
        for n_down in 1usize..=3 {
            if n_up + n_down + 1 >= 3 {
                make_test(
                    vec![1; n_up], vec![1; n_down], 0, 0,
                    &mut out, &mut seen, &mut count, goal,
                );
            }
        }
    }

    // ---- Peak at leftmost valid position (index 1) ----
    for n_down in [1usize, 5, 50, 500] {
        make_test(
            vec![n_down as i32 + 1], vec![1; n_down], 0, 0,
            &mut out, &mut seen, &mut count, goal,
        );
    }

    // ---- Peak at rightmost valid position (second-to-last) ----
    for n_up in [1usize, 5, 50, 500] {
        make_test(
            vec![1; n_up], vec![n_up as i32 + 1], 0, 0,
            &mut out, &mut seen, &mut count, goal,
        );
    }

    // ---- Symmetric mountains ----
    for half in [1usize, 5, 50, 500] {
        make_test(
            vec![1; half], vec![1; half], 0, 0,
            &mut out, &mut seen, &mut count, goal,
        );
    }

    // ---- Large values near 1_000_000 ----
    make_test(vec![999_999], vec![999_999], 0, 0, &mut out, &mut seen, &mut count, goal);
    make_test(vec![500_000], vec![500_000], 0, 0, &mut out, &mut seen, &mut count, goal);
    make_test(vec![1], vec![1], 999_998, 0, &mut out, &mut seen, &mut count, goal);

    // ---- Steep ascent, gentle descent ----
    make_test(vec![100], vec![1; 100], 0, 0, &mut out, &mut seen, &mut count, goal);

    // ---- Gentle ascent, steep descent ----
    make_test(vec![1; 100], vec![100], 0, 0, &mut out, &mut seen, &mut count, goal);

    // ---- Random small arrays (3-10 elements) ----
    for _ in 0..10 {
        let total = rng.gen_range_usize(3, 10);
        let n_up = rng.gen_range_usize(1, total - 2);
        let n_down = total - 1 - n_up;
        let max_peak: i64 = 1_000_000 / std::cmp::max(n_up, 1) as i64;
        let max_d = std::cmp::max(1, std::cmp::min(max_peak, 1000) as i32);
        let up = random_deltas(&mut rng, n_up, max_d);
        let up_sum: i64 = up.iter().map(|d| *d as i64).sum();
        let base_hi = std::cmp::min(1_000_000i64, 1_000_000 - up_sum);
        let base = if base_hi < 0 { 0 } else { rng.gen_range_i64(0, base_hi) as i32 };
        let peak_val = base as i64 + up_sum;
        let max_dd = std::cmp::max(1, std::cmp::min(peak_val / std::cmp::max(n_down, 1) as i64, 1000)) as i32;
        let down = random_deltas(&mut rng, n_down, max_dd);
        let down_sum: i64 = down.iter().map(|d| *d as i64).sum();
        if down_sum <= peak_val {
            for mk in 0u8..=1 {
                make_test(up.clone(), down.clone(), base, mk, &mut out, &mut seen, &mut count, goal);
            }
        }
    }

    // ---- Random medium arrays (10-500 elements) ----
    for _ in 0..10 {
        let total = rng.gen_range_usize(10, 500);
        let n_up = rng.gen_range_usize(1, total - 2);
        let n_down = total - 1 - n_up;
        let max_d = std::cmp::max(1, std::cmp::min(1_000_000i64 / std::cmp::max(n_up, 1) as i64, 100)) as i32;
        let up = random_deltas(&mut rng, n_up, max_d);
        let up_sum: i64 = up.iter().map(|d| *d as i64).sum();
        let base_hi = 1_000_000i64 - up_sum;
        let base = if base_hi < 0 { 0 } else { rng.gen_range_i64(0, std::cmp::min(base_hi, 1_000_000)) as i32 };
        let peak_val = base as i64 + up_sum;
        let max_dd = std::cmp::max(1, std::cmp::min(peak_val / std::cmp::max(n_down, 1) as i64, 100)) as i32;
        let down = random_deltas(&mut rng, n_down, max_dd);
        let down_sum: i64 = down.iter().map(|d| *d as i64).sum();
        if down_sum <= peak_val {
            make_test(up, down, base, 0, &mut out, &mut seen, &mut count, goal);
        }
    }

    // ---- Random large arrays (1000-10000 elements) ----
    for _ in 0..5 {
        let total = rng.gen_range_usize(1000, 10000);
        let n_up = rng.gen_range_usize(1, total - 2);
        let n_down = total - 1 - n_up;
        // Use all-1 deltas for large arrays to stay within value bounds
        let up = vec![1i32; n_up];
        let down = vec![1i32; n_down];
        let up_sum = n_up as i64;
        let base_hi = 1_000_000i64 - up_sum;
        let base = if base_hi < 0 { 0 } else {
            let peak_val = base_hi + up_sum;
            let need_base = if n_down as i64 > peak_val { 0 } else { 0 };
            // Ensure peak_val - n_down >= 0 => base >= n_down - n_up
            let min_base = std::cmp::max(0, n_down as i64 - up_sum);
            if min_base > base_hi { continue; }
            rng.gen_range_i64(min_base, base_hi) as i32
        };
        make_test(up, down, base, 0, &mut out, &mut seen, &mut count, goal);
    }

    // ---- Maximum size (100_000 elements) ----
    {
        let n_up = 49_999;
        let n_down = 50_000;
        let base = n_down as i32; // peak_val = base + n_up, last_val = peak_val - n_down = n_up - 1 >= 0
        if base as i64 + n_up as i64 <= 1_000_000 {
            make_test(vec![1; n_up], vec![1; n_down], base, 0, &mut out, &mut seen, &mut count, goal);
        }
    }
    {
        let n_up = 50_000;
        let n_down = 49_999;
        let base = n_down as i32;
        if base as i64 + n_up as i64 <= 1_000_000 {
            make_test(vec![1; n_up], vec![1; n_down], base, 0, &mut out, &mut seen, &mut count, goal);
        }
    }

    // ---- Fill remaining with random sizes and mutations ----
    while count < goal {
        let total = match count % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let n_up = rng.gen_range_usize(1, total - 2);
        let n_down = total - 1 - n_up;
        let max_d = std::cmp::max(1,
            std::cmp::min(1_000_000i64 / std::cmp::max(n_up, 1) as i64, 50)) as i32;
        let up = random_deltas(&mut rng, n_up, max_d);
        let up_sum: i64 = up.iter().map(|d| *d as i64).sum();
        let base_hi = 1_000_000i64 - up_sum;
        if base_hi < 0 { continue; }
        let peak_val_max = base_hi + up_sum;
        let min_base = std::cmp::max(0, n_down as i64);
        if min_base > base_hi { continue; }
        let base = rng.gen_range_i64(min_base, base_hi) as i32;
        let peak_val = base as i64 + up_sum;
        let max_dd = std::cmp::max(1,
            std::cmp::min(peak_val / std::cmp::max(n_down, 1) as i64, 50)) as i32;
        let down = random_deltas(&mut rng, n_down, max_dd);
        let down_sum: i64 = down.iter().map(|d| *d as i64).sum();
        if down_sum > peak_val { continue; }
        let mk = (rng.next_u64() % 2) as u8;
        make_test(up, down, base, mk, &mut out, &mut seen, &mut count, goal);
    }
}
