use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 1.
proof fn lemma_sum_deltas_mono(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i64,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// Two partial sums differ by at least (b - a) when every delta >= 1.
proof fn lemma_sum_deltas_strict(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i64,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

pub fn generate_test_case(
    x_deltas: &Vec<i64>,
    base: i64,
    h_vals: &Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        h_vals.len() >= 1,
        h_vals.len() <= 100_000,
        x_deltas.len() + 1 == h_vals.len(),
        1 <= base,
        forall|i: int| 0 <= i < x_deltas.len() ==> 1 <= #[trigger] x_deltas[i],
        base as int + sum_deltas(x_deltas@, x_deltas.len() as int) <= 1_000_000_000,
        forall|i: int| 0 <= i < h_vals.len() ==> 1 <= #[trigger] h_vals[i] <= 1_000_000_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0@[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1@[j] <= 1_000_000_000,
        forall|j: int| 0 <= j < result.0.len() - 1 ==> result.0@[j] < #[trigger] result.0@[j + 1],
{
    // Build x from base + cumulative deltas
    let mut x: Vec<i64> = Vec::new();

    proof {
        lemma_sum_deltas_mono(x_deltas@, 0, x_deltas.len() as int);
        assert(sum_deltas(x_deltas@, 0) == 0);
        assert(base as int <= 1_000_000_000);
    }

    x.push(base);

    let mut i: usize = 0;
    while i < x_deltas.len()
        invariant
            0 <= i <= x_deltas.len(),
            x.len() == i + 1,
            x_deltas.len() + 1 == h_vals.len(),
            x_deltas.len() + 1 <= 100_000,
            1 <= base,
            forall|k: int| 0 <= k < x_deltas.len() ==> #[trigger] x_deltas[k] >= 1i64,
            base as int + sum_deltas(x_deltas@, x_deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] x[k] as int == base as int + sum_deltas(x_deltas@, k),
            forall|k: int| 0 <= k < x.len() ==> 1 <= #[trigger] x[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < x.len() ==> x[k] < x[l],
        decreases x_deltas.len() - i,
    {
        let ghost old_len = x.len();

        proof {
            lemma_sum_deltas_mono(x_deltas@, (i + 1) as int, x_deltas.len() as int);
        }

        let next = x[i] + x_deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(x_deltas@, (i + 1) as int));
            assert(1 <= next <= 1_000_000_000) by {
                lemma_sum_deltas_mono(x_deltas@, 0, (i + 1) as int);
                assert(sum_deltas(x_deltas@, (i + 1) as int) >= 0);
                assert(base as int + sum_deltas(x_deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(x_deltas@, x_deltas.len() as int));
            };

            assert forall|k: int| 0 <= k < x.len() implies x[k] < next by {
                assert(x[k] as int == base as int + sum_deltas(x_deltas@, k));
                assert(next as int == base as int + sum_deltas(x_deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(x_deltas@, k, (i + 1) as int);
            };
        }

        x.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < x.len() implies x[k] < x[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(x[l] == next);
                }
            };
        }
    }

    // Build h based on mutation_kind
    let mut h: Vec<i64> = Vec::new();

    if mutation_kind == 1 {
        // All heights = 1
        let mut j: usize = 0;
        while j < h_vals.len()
            invariant
                0 <= j <= h_vals.len(),
                h.len() == j,
                forall|k: int| 0 <= k < h.len() ==> 1 <= #[trigger] h@[k] <= 1_000_000_000,
            decreases h_vals.len() - j,
        {
            h.push(1i64);
            j = j + 1;
        }
    } else if mutation_kind == 2 {
        // All heights = h_vals[0]
        let h0 = h_vals[0];
        let mut j: usize = 0;
        while j < h_vals.len()
            invariant
                0 <= j <= h_vals.len(),
                h.len() == j,
                1 <= h0 <= 1_000_000_000,
                forall|k: int| 0 <= k < h.len() ==> 1 <= #[trigger] h@[k] <= 1_000_000_000,
            decreases h_vals.len() - j,
        {
            h.push(h0);
            j = j + 1;
        }
    } else {
        // Identity: copy h_vals
        let mut j: usize = 0;
        while j < h_vals.len()
            invariant
                0 <= j <= h_vals.len(),
                h.len() == j,
                forall|k: int| 0 <= k < h_vals.len() ==> 1 <= #[trigger] h_vals[k] <= 1_000_000_000,
                forall|k: int| 0 <= k < h.len() ==> 1 <= #[trigger] h@[k] <= 1_000_000_000,
            decreases h_vals.len() - j,
        {
            h.push(h_vals[j]);
            j = j + 1;
        }
    }

    assert(x.len() == h_vals.len()) by {
        assert(x.len() == x_deltas.len() + 1);
    };
    assert(h.len() == h_vals.len());

    // Prove ensures about x@ using x invariants
    proof {
        assert forall|j: int| 0 <= j < x.len() implies 1 <= #[trigger] x@[j] <= 1_000_000_000 by {
            assert(1 <= x[j] <= 1_000_000_000);
        };
        assert forall|j: int| 0 <= j < x.len() - 1 implies x@[j] < #[trigger] x@[j + 1] by {
            assert(x[j] < x[j + 1]);
        };
    }

    (x, h)
}

}

use std::io::Write;
use std::collections::HashSet;

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

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(x: &[i64], h: &[i64]) -> String {
    let n = x.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", x[i], h[i]));
    }
    s
}

fn random_trees(rng: &mut Rng, n: usize) -> (Vec<i64>, Vec<i64>) {
    // Strictly increasing distinct x
    let mut xs: HashSet<i64> = HashSet::new();
    while xs.len() < n {
        xs.insert(rng.gen_range_i64(1, 1_000_000_000));
    }
    let mut x: Vec<i64> = xs.into_iter().collect();
    x.sort();
    let h: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
    (x, h)
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(545);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |x: Vec<i64>, h: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if x.is_empty() || x.len() != h.len() { return; }
        for i in 1..x.len() {
            if x[i] <= x[i-1] { return; }
        }
        for &xi in &x { if xi < 1 || xi > 1_000_000_000 { return; } }
        for &hi in &h { if hi < 1 || hi > 1_000_000_000 { return; } }
        let key = format!("{:?}_{:?}", x, h);
        if !seen.insert(key) { return; }
        let result = Solution::max_felled_trees(x.clone(), h.clone());
        let inp = build_input(&x, &h);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(vec![1, 2, 5, 10, 19], vec![2, 1, 10, 9, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 5, 10, 20], vec![2, 1, 10, 9, 1], &mut seen, &mut out, &mut count);

    // Edge
    emit(vec![1], vec![1], &mut seen, &mut out, &mut count);
    emit(vec![5], vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1, 2], vec![1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 1_000_000_000], vec![1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 5, 9], vec![3, 3, 3], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 2000),
            _ => rng.gen_range_usize(1000, 5000),
        };
        let (x, h) = random_trees(&mut rng, n);
        emit(x, h, &mut seen, &mut out, &mut count);
    }
}

