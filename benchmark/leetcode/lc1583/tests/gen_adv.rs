use vstd::prelude::*;

verus! {

pub open spec fn pref_value(a: int, j: int, n: int) -> int
    recommends
        0 < n,
{
    if j < a {
        j
    } else {
        j + 1
    }
}

// Build preferences row for person i: lists all j in [0,n) with j != i.
// We use the canonical increasing order: 0, 1, ..., i-1, i+1, ..., n-1.

pub fn generate_test_case(n: i32) -> (result: (i32, Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        2 <= n <= 500,
        n % 2 == 0,
    ensures
        ({
            let rn = result.0;
            let preferences = result.1;
            let pairs = result.2;
            &&& rn == n
            &&& 2 <= rn <= 500
            &&& rn % 2 == 0
            &&& preferences.len() == rn
            &&& (forall |i: int| 0 <= i < rn ==> (#[trigger] preferences[i]).len() == rn - 1)
            &&& (forall |i: int, j: int| 0 <= i < rn && 0 <= j < rn - 1 ==>
                    0 <= #[trigger] preferences[i][j] <= rn - 1)
            &&& (forall |i: int, j: int| 0 <= i < rn && 0 <= j < rn - 1 ==>
                    preferences[i][j] != i as i32)
            &&& (forall |i: int, j1: int, j2: int| 0 <= i < rn && 0 <= j1 < rn - 1 && 0 <= j2 < rn - 1 && j1 != j2 ==>
                    #[trigger] preferences[i][j1] != #[trigger] preferences[i][j2])
            &&& pairs.len() == rn / 2
            &&& (forall |k: int| 0 <= k < rn / 2 ==>
                    (#[trigger] pairs[k]).len() == 2
                    && 0 <= pairs[k][0] <= rn - 1
                    && 0 <= pairs[k][1] <= rn - 1
                    && pairs[k][0] != pairs[k][1])
            &&& (forall |k1: int, k2: int| 0 <= k1 < k2 < rn / 2 ==>
                    (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
                    && pairs[k1][0] != pairs[k2][1]
                    && pairs[k1][1] != pairs[k2][0]
                    && pairs[k1][1] != pairs[k2][1])
        }),
{
    let nu: usize = n as usize;

    // Build preferences.
    let mut preferences: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < nu
        invariant
            nu == n as usize,
            2 <= n <= 500,
            i <= nu,
            preferences.len() == i,
            forall |a: int| 0 <= a < i as int ==> (#[trigger] preferences[a]).len() == n - 1,
            forall |a: int, j: int| 0 <= a < i as int && 0 <= j < n - 1 ==>
                #[trigger] preferences[a][j] == pref_value(a, j, n as int) as i32,
        decreases nu - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nu - 1
            invariant
                nu == n as usize,
                2 <= n <= 500,
                i < nu,
                j <= nu - 1,
                row.len() == j,
                forall |k: int| 0 <= k < j as int ==>
                    #[trigger] row[k] == pref_value(i as int, k, n as int) as i32,
            decreases (nu - 1) - j,
        {
            let v: i32 = if j < i {
                j as i32
            } else {
                (j + 1) as i32
            };
            row.push(v);
            assert(row[j as int] == pref_value(i as int, j as int, n as int) as i32);
            j = j + 1;
        }
        preferences.push(row);
        i = i + 1;
    }

    // Build pairs: pair (2k, 2k+1) for k in 0..n/2.
    let mut pairs: Vec<Vec<i32>> = Vec::new();
    let half: usize = nu / 2;
    let mut k: usize = 0;
    while k < half
        invariant
            nu == n as usize,
            2 <= n <= 500,
            half == nu / 2,
            k <= half,
            pairs.len() == k,
            forall |a: int| 0 <= a < k as int ==>
                (#[trigger] pairs[a]).len() == 2
                && pairs[a][0] == (2 * a) as i32
                && pairs[a][1] == (2 * a + 1) as i32,
        decreases half - k,
    {
        let mut p: Vec<i32> = Vec::new();
        p.push((2 * k) as i32);
        p.push((2 * k + 1) as i32);
        pairs.push(p);
        k = k + 1;
    }

    // Proofs.
    proof {
        let rn: int = n as int;

        // preferences[i][j] != i
        assert forall |a: int, j: int| 0 <= a < rn && 0 <= j < rn - 1 implies
            preferences[a][j] != a as i32
        by {
            let v = pref_value(a, j, rn) as i32;
            assert(preferences[a][j] == v);
            if j < a {
                assert(v as int == j);
                assert(j < a);
            } else {
                assert(v as int == j + 1);
                assert(j + 1 > a);
            }
        }

        // preferences[i][j1] != preferences[i][j2] when j1 != j2
        assert forall |a: int, j1: int, j2: int|
            0 <= a < rn && 0 <= j1 < rn - 1 && 0 <= j2 < rn - 1 && j1 != j2 implies
            #[trigger] preferences[a][j1] != #[trigger] preferences[a][j2]
        by {
            let v1 = pref_value(a, j1, rn) as i32;
            let v2 = pref_value(a, j2, rn) as i32;
            assert(preferences[a][j1] == v1);
            assert(preferences[a][j2] == v2);
            if j1 < a {
                if j2 < a {
                    assert(v1 as int == j1);
                    assert(v2 as int == j2);
                } else {
                    assert(v1 as int == j1);
                    assert(v2 as int == j2 + 1);
                    assert((v1 as int) < a);
                    assert((v2 as int) > a);
                }
            } else {
                if j2 < a {
                    assert(v1 as int == j1 + 1);
                    assert(v2 as int == j2);
                    assert((v1 as int) > a);
                    assert((v2 as int) < a);
                } else {
                    assert(v1 as int == j1 + 1);
                    assert(v2 as int == j2 + 1);
                }
            }
        }

        // pairs properties
        assert forall |kk: int| 0 <= kk < rn / 2 implies
            (#[trigger] pairs[kk]).len() == 2
            && 0 <= pairs[kk][0] <= rn - 1
            && 0 <= pairs[kk][1] <= rn - 1
            && pairs[kk][0] != pairs[kk][1]
        by {
            assert(pairs[kk][0] == (2 * kk) as i32);
            assert(pairs[kk][1] == (2 * kk + 1) as i32);
        }

        assert forall |k1: int, k2: int| 0 <= k1 < k2 < rn / 2 implies
            (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
            && pairs[k1][0] != pairs[k2][1]
            && pairs[k1][1] != pairs[k2][0]
            && pairs[k1][1] != pairs[k2][1]
        by {
            assert(pairs[k1][0] == (2 * k1) as i32);
            assert(pairs[k1][1] == (2 * k1 + 1) as i32);
            assert(pairs[k2][0] == (2 * k2) as i32);
            assert(pairs[k2][1] == (2 * k2 + 1) as i32);
        }

    }

    let result = (n, preferences, pairs);
    proof {
        let rn = result.0;
        let preferences = result.1;
        let pairs = result.2;
        assert(rn == n);
        assert(2 <= rn <= 500);
        assert(rn % 2 == 0);
        assert(preferences.len() == rn);
        assert forall |i: int| 0 <= i < rn implies (#[trigger] preferences[i]).len() == rn - 1 by {}
        assert forall |i: int, j: int| 0 <= i < rn && 0 <= j < rn - 1 implies
            0 <= #[trigger] preferences[i][j] <= rn - 1 by {}
        assert forall |i: int, j: int| 0 <= i < rn && 0 <= j < rn - 1 implies
            preferences[i][j] != i as i32 by {}
        assert forall |i: int, j1: int, j2: int|
            0 <= i < rn && 0 <= j1 < rn - 1 && 0 <= j2 < rn - 1 && j1 != j2 implies
            #[trigger] preferences[i][j1] != #[trigger] preferences[i][j2] by {}
        assert(pairs.len() == rn / 2);
        assert forall |k: int| 0 <= k < rn / 2 implies
            (#[trigger] pairs[k]).len() == 2
            && 0 <= pairs[k][0] <= rn - 1
            && 0 <= pairs[k][1] <= rn - 1
            && pairs[k][0] != pairs[k][1] by {}
        assert forall |k1: int, k2: int| 0 <= k1 < k2 < rn / 2 implies
            (#[trigger] pairs[k1])[0] != (#[trigger] pairs[k2])[0]
            && pairs[k1][0] != pairs[k2][1]
            && pairs[k1][1] != pairs[k2][0]
            && pairs[k1][1] != pairs[k2][1] by {}
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn print_case(n: i32, preferences: &Vec<Vec<i32>>, pairs: &Vec<Vec<i32>>) {
    print!("{{\"n\":{},\"preferences\":[", n);
    for i in 0..preferences.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..preferences[i].len() {
            if j > 0 { print!(","); }
            print!("{}", preferences[i][j]);
        }
        print!("]");
    }
    print!("],\"pairs\":[");
    for k in 0..pairs.len() {
        if k > 0 { print!(","); }
        print!("[{},{}]", pairs[k][0], pairs[k][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 10;
        // n must be even, 2 <= n <= 500
        let n: i32 = match mode {
            0 => 2,
            1 => 4,
            2 => 500,
            3 => 498,
            4 => 10,
            5 => 100,
            6 => 50,
            7 => 250,
            8 => {
                let r = rng.gen_range_usize(1, 250);
                (r * 2) as i32
            }
            _ => {
                let r = rng.gen_range_usize(1, 250);
                (r * 2) as i32
            }
        };

        let (rn, prefs, pairs) = generate_test_case(n);
        print_case(rn, &prefs, &pairs);
    }
}
