use vstd::prelude::*;

verus! {

pub fn generate_test_case(mutation_kind: u8) -> (result: (i32, Vec<Vec<i32>>, Vec<Vec<i32>>))
    ensures
        2 <= result.0 <= 500,
        result.0 % 2 == 0,
        result.1.len() == result.0,
        forall |i: int| 0 <= i < result.0 ==> (#[trigger] result.1[i]).len() == result.0 - 1,
        forall |i: int, j: int| 0 <= i < result.0 && 0 <= j < result.0 - 1 ==>
            0 <= #[trigger] result.1[i][j] <= result.0 - 1,
        forall |i: int, j: int| 0 <= i < result.0 && 0 <= j < result.0 - 1 ==>
            result.1[i][j] != i as i32,
        forall |i: int, j1: int, j2: int| 0 <= i < result.0 && 0 <= j1 < result.0 - 1 && 0 <= j2 < result.0 - 1 && j1 != j2 ==>
            #[trigger] result.1[i][j1] != #[trigger] result.1[i][j2],
        forall |i: int, u: int| #![trigger result.1[i], result.1[u]]
            0 <= i < result.0 && 0 <= u < result.0 && u != i ==>
            exists |j: int| 0 <= j < result.0 - 1 && result.1[i][j] == u as i32,
        result.2.len() == result.0 / 2,
        forall |k: int| 0 <= k < result.0 / 2 ==>
            (#[trigger] result.2[k]).len() == 2
            && 0 <= result.2[k][0] <= result.0 - 1
            && 0 <= result.2[k][1] <= result.0 - 1
            && result.2[k][0] != result.2[k][1],
        forall |k1: int, k2: int| 0 <= k1 < k2 < result.0 / 2 ==>
            (#[trigger] result.2[k1])[0] != (#[trigger] result.2[k2])[0]
            && result.2[k1][0] != result.2[k2][1]
            && result.2[k1][1] != result.2[k2][0]
            && result.2[k1][1] != result.2[k2][1],
        forall |x: int| #![trigger result.1[x]]
            0 <= x < result.0 ==>
            exists |k: int| 0 <= k < result.0 / 2 && (result.2[k][0] as int == x || result.2[k][1] as int == x),
{
    if mutation_kind == 1 {
        // n=2, preferences=[[1],[0]], pairs=[[1,0]]
        let mut pref0: Vec<i32> = Vec::new(); pref0.push(1);
        let mut pref1: Vec<i32> = Vec::new(); pref1.push(0);
        let mut prefs: Vec<Vec<i32>> = Vec::new(); prefs.push(pref0); prefs.push(pref1);
        let mut pair0: Vec<i32> = Vec::new(); pair0.push(1); pair0.push(0);
        let mut ps: Vec<Vec<i32>> = Vec::new(); ps.push(pair0);
        proof {
            assert(prefs[0 as int][0] == 1i32); assert(prefs[1 as int][0] == 0i32);
            assert forall |i: int, u: int| #![trigger prefs[i], prefs[u]] 0 <= i < 2 && 0 <= u < 2 && u != i implies exists |j: int| 0 <= j < 1 && prefs[i][j] == u as i32 by { assert(prefs[i][0] == u as i32); };
            assert forall |x: int| #![trigger prefs[x]] 0 <= x < 2 implies exists |k: int| 0 <= k < 1 && (ps[k][0] as int == x || ps[k][1] as int == x) by { if x == 0 { assert(ps[0 as int][1] as int == 0); } else { assert(ps[0 as int][0] as int == 1); } };
        }
        (2i32, prefs, ps)
    } else {
        // n=2, preferences=[[1],[0]], pairs=[[0,1]]
        let mut pref0: Vec<i32> = Vec::new(); pref0.push(1);
        let mut pref1: Vec<i32> = Vec::new(); pref1.push(0);
        let mut prefs: Vec<Vec<i32>> = Vec::new(); prefs.push(pref0); prefs.push(pref1);
        let mut pair0: Vec<i32> = Vec::new(); pair0.push(0); pair0.push(1);
        let mut ps: Vec<Vec<i32>> = Vec::new(); ps.push(pair0);
        proof {
            assert(prefs[0 as int][0] == 1i32); assert(prefs[1 as int][0] == 0i32);
            assert forall |i: int, u: int| #![trigger prefs[i], prefs[u]] 0 <= i < 2 && 0 <= u < 2 && u != i implies exists |j: int| 0 <= j < 1 && prefs[i][j] == u as i32 by { assert(prefs[i][0] == u as i32); };
            assert forall |x: int| #![trigger prefs[x]] 0 <= x < 2 implies exists |k: int| 0 <= k < 1 && (ps[k][0] as int == x || ps[k][1] as int == x) by { if x == 0 { assert(ps[0 as int][0] as int == 0); } else { assert(ps[0 as int][1] as int == 1); } };
        }
        (2i32, prefs, ps)
    }
}

} // verus!

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); self.0 }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize { assert!(lo <= hi); lo + (self.next_u64() as usize) % (hi - lo + 1) }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn shuffle(v: &mut Vec<i32>, rng: &mut Rng) { let n = v.len(); for i in (1..n).rev() { let j = rng.gen_range_usize(0, i); v.swap(i, j); } }
fn canonical_preferences(n: usize) -> Vec<Vec<i32>> { let mut p = Vec::with_capacity(n); for i in 0..n { let mut r = Vec::with_capacity(n-1); for j in 0..n { if j != i { r.push(j as i32); } } p.push(r); } p }
fn canonical_pairs(n: usize) -> Vec<Vec<i32>> { let mut p = Vec::with_capacity(n/2); let mut k = 0; while k < n { p.push(vec![k as i32, (k+1) as i32]); k += 2; } p }
fn random_preferences(n: usize, rng: &mut Rng) -> Vec<Vec<i32>> { let mut p = canonical_preferences(n); for row in p.iter_mut() { shuffle(row, rng); } p }
fn random_pairs(n: usize, rng: &mut Rng) -> Vec<Vec<i32>> { let mut ppl: Vec<i32> = (0..n as i32).collect(); shuffle(&mut ppl, rng); let mut p = Vec::with_capacity(n/2); let mut k = 0; while k < n { p.push(vec![ppl[k], ppl[k+1]]); k += 2; } p }

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1583);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, prefs: Vec<Vec<i32>>, pairs: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let result = Solution::unhappy_friends(n, prefs.clone(), pairs.clone());
        let line = json!({"input": {"n": n, "preferences": prefs, "pairs": pairs}, "output": result}).to_string();
        if seen.insert(line.clone()) { writeln!(out, "{}", line).unwrap(); *count += 1; }
    };

    // Verified constructions
    for mk in 0u8..=1 { let (n,p,q) = generate_test_case(mk); emit(n, p, q, &mut seen, &mut out, &mut count); }

    // LeetCode examples
    emit(4, vec![vec![1,2,3],vec![3,2,0],vec![3,1,0],vec![1,2,0]], vec![vec![0,1],vec![2,3]], &mut seen, &mut out, &mut count);
    emit(2, vec![vec![1],vec![0]], vec![vec![1,0]], &mut seen, &mut out, &mut count);
    emit(4, vec![vec![1,3,2],vec![2,3,0],vec![1,3,0],vec![0,2,1]], vec![vec![1,3],vec![0,2]], &mut seen, &mut out, &mut count);

    // Canonical, various sizes
    for &n in &[2,4,6,8,10,20,50,100] { emit(n, canonical_preferences(n as usize), canonical_pairs(n as usize), &mut seen, &mut out, &mut count); }
    // Reversed prefs
    for &n in &[4,6,8,10,20] { let mut p = canonical_preferences(n as usize); for r in p.iter_mut() { r.reverse(); } emit(n, p, canonical_pairs(n as usize), &mut seen, &mut out, &mut count); }
    // Cross-pairing
    for &n in &[4,6,8,10,20] { let mut pairs = Vec::new(); for i in 0..(n/2) as usize { pairs.push(vec![i as i32, (n as usize-1-i) as i32]); } emit(n, canonical_preferences(n as usize), pairs, &mut seen, &mut out, &mut count); }
    // Random small
    for _ in 0..10 { let n = 2*rng.gen_range_usize(1,3); emit(n as i32, random_preferences(n,&mut rng), random_pairs(n,&mut rng), &mut seen, &mut out, &mut count); }
    // Random medium
    for _ in 0..20 { let n = 2*rng.gen_range_usize(4,25); emit(n as i32, random_preferences(n,&mut rng), random_pairs(n,&mut rng), &mut seen, &mut out, &mut count); }
    // Random large
    for _ in 0..10 { let n = 2*rng.gen_range_usize(50,250); emit(n as i32, random_preferences(n,&mut rng), random_pairs(n,&mut rng), &mut seen, &mut out, &mut count); }
    // Boundary n=500
    { let n=500; emit(n as i32, random_preferences(n,&mut rng), random_pairs(n,&mut rng), &mut seen, &mut out, &mut count); }
    // Fill remaining
    while count < goal { let n = 2*rng.gen_range_usize(1,100); emit(n as i32, random_preferences(n,&mut rng), random_pairs(n,&mut rng), &mut seen, &mut out, &mut count); }
}
