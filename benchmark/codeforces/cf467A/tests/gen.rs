use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    p: Vec<i64>,
    q: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= p.len() && p.len() <= 100,
        p.len() == q.len(),
        forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p[j] as int) && (p[j] as int) <= (q[j] as int) && (q[j] as int) <= 100,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall|j: int| 0 <= j < result.0.len() ==> 0 <= (#[trigger] result.0[j] as int) && (result.0[j] as int) <= (result.1[j] as int) && (result.1[j] as int) <= 100,
{
    let n = p.len();
    if mutation_kind == 0 {
        // identity
        (p, q)
    } else if mutation_kind == 1 {
        // set first p to 0
        let mut dp = p;
        dp.set(0, 0);
        (dp, q)
    } else if mutation_kind == 2 {
        // set first q to 100
        let mut dq = q;
        dq.set(0, 100);
        (p, dq)
    } else if mutation_kind == 3 {
        // set first p = q (room can't fit two)
        let mut dp = p;
        dp.set(0, q[0]);
        (dp, q)
    } else if mutation_kind == 4 {
        // set first p to 0, q to 100 (max gap)
        let mut dp = p;
        let mut dq = q;
        dp.set(0, 0);
        dq.set(0, 100);
        (dp, dq)
    } else if mutation_kind == 5 {
        // set all p to 0
        let mut dp = p;
        proof {
            assert forall|j: int| 0 <= j < q.len() implies 0 <= (#[trigger] q@[j] as int) && (q@[j] as int) <= 100 by {
                assert(0 <= (#[trigger] dp@[j] as int));  // fires original trigger on p
            }
        }
        let mut i: usize = 0;
        while i < dp.len()
            invariant
                0 <= i <= dp.len(),
                dp.len() == n,
                q.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> dp[j] == 0i64,
                forall|j: int| #![trigger dp@[j]] i <= j < dp.len() as int ==> dp@[j] == p@[j],
                forall|j: int| 0 <= j < q.len() ==> 0 <= (#[trigger] q@[j] as int) && (q@[j] as int) <= 100,
            decreases dp.len() - i,
        {
            dp.set(i, 0);
            i += 1;
        }
        (dp, q)
    } else if mutation_kind == 6 {
        // set all q to 100
        let mut dq = q;
        let mut i: usize = 0;
        while i < dq.len()
            invariant
                0 <= i <= dq.len(),
                dq.len() == n,
                p.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> dq[j] == 100i64,
                forall|j: int| #![trigger dq@[j]] i <= j < dq.len() as int ==> dq@[j] == q@[j],
                forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p@[j] as int) && (p@[j] as int) <= 100,
            decreases dq.len() - i,
        {
            dq.set(i, 100);
            i += 1;
        }
        (p, dq)
    } else if mutation_kind == 7 {
        // set all p = q (no room fits two)
        let mut dp = p;
        proof {
            assert forall|j: int| 0 <= j < q.len() implies 0 <= (#[trigger] q@[j] as int) && (q@[j] as int) <= 100 by {
                assert(0 <= (#[trigger] dp@[j] as int));
            }
        }
        let mut i: usize = 0;
        while i < dp.len()
            invariant
                0 <= i <= dp.len(),
                dp.len() == n,
                q.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> dp[j] == q@[j],
                forall|j: int| #![trigger dp@[j]] i <= j < dp.len() as int ==> dp@[j] == p@[j],
                forall|j: int| 0 <= j < q.len() ==> 0 <= (#[trigger] q@[j] as int) && (q@[j] as int) <= 100,
            decreases dp.len() - i,
        {
            dp.set(i, q[i]);
            i += 1;
        }
        (dp, q)
    } else if mutation_kind == 8 {
        // set all p to 0 and q to 100 (all rooms fit two)
        let mut dp = p;
        let mut dq = q;
        let mut i: usize = 0;
        while i < dp.len()
            invariant
                0 <= i <= dp.len(),
                dp.len() == n,
                dq.len() == n,
                1 <= n <= 100,
                forall|j: int| 0 <= j < i ==> dp[j] == 0i64,
                forall|j: int| 0 <= j < i ==> dq[j] == 100i64,
                forall|j: int| #![trigger dp@[j]] i <= j < dp.len() as int ==> dp@[j] == p@[j],
                forall|j: int| #![trigger dq@[j]] i <= j < dq.len() as int ==> dq@[j] == q@[j],
            decreases dp.len() - i,
        {
            dp.set(i, 0);
            dq.set(i, 100);
            i += 1;
        }
        (dp, dq)
    } else if mutation_kind == 9 && p.len() >= 2 {
        // swap first two elements of p (preserves constraint if q also swapped)
        let mut dp = p;
        let mut dq = q;
        let tmp_p = dp[0];
        let tmp_q = dq[0];
        dp.set(0, dp[1]);
        dq.set(0, dq[1]);
        dp.set(1, tmp_p);
        dq.set(1, tmp_q);
        (dp, dq)
    } else if mutation_kind == 10 {
        // nudge first p down (if > 0)
        let mut dp = p;
        if dp[0] > 0 {
            dp.set(0, dp[0] - 1);
        }
        (dp, q)
    } else if mutation_kind == 11 {
        // nudge first q up (if < 100)
        let mut dq = q;
        if dq[0] < 100 {
            dq.set(0, dq[0] + 1);
        }
        (p, dq)
    } else {
        // fallback: identity
        (p, q)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
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

fn build_input(p: &[i64], q: &[i64]) -> String {
    let n = p.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", p[i], q[i]));
    }
    s
}

fn random_pq(rng: &mut Rng) -> (i64, i64) {
    let q = rng.gen_range_i64(0, 100);
    let p = rng.gen_range_i64(0, q);
    (p, q)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |p: Vec<i64>, q: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = p.len();
        if !(1 <= n && n <= 100 && q.len() == n) { return; }
        for i in 0..n {
            if !(0 <= p[i] && p[i] <= q[i] && q[i] <= 100) { return; }
        }
        let key = format!("{:?}|{:?}", p, q);
        if !seen.insert(key) { return; }
        let inp = build_input(&p, &q);
        let ans = Solution::count_accommodation_rooms(p.clone(), q.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![1, 2, 3], vec![1, 2, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 0, 10], vec![10, 10, 10], &mut seen, &mut out, &mut count);
    emit(vec![0], vec![100], &mut seen, &mut out, &mut count);
    emit(vec![100], vec![100], &mut seen, &mut out, &mut count);
    emit(vec![0; 100], vec![100; 100], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let mut p = Vec::with_capacity(n);
        let mut q = Vec::with_capacity(n);
        for _ in 0..n {
            let (pi, qi) = random_pq(&mut rng);
            p.push(pi);
            q.push(qi);
        }
        emit(p, q, &mut seen, &mut out, &mut count);
    }
}

