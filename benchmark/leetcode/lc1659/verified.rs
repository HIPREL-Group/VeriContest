use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow3(k: int) -> int
    decreases k
{
    if k <= 0 { 1 } else { 3 * pow3(k - 1) }
}

pub open spec fn interaction(me: int, neighbor: int) -> int {
    if neighbor == 0 || me == 0 { 0 }
    else if me == 1 && neighbor == 1 { -60 }
    else if me == 1 && neighbor == 2 { -10 }
    else if me == 2 && neighbor == 1 { -10 }
    else { 40 }
}

pub open spec fn delta_spec(t: int, pos: int, profile: int, m: int, n: int) -> int {
    let row = pos / n;
    let col = pos % n;
    let up_type = profile % 3;
    let left_type = (profile / pow3(n - 1)) % 3;
    let base: int = if t == 1 { 120 } else if t == 2 { 40 } else { 0 };
    base
    + (if row > 0 { interaction(t, up_type) } else { 0 })
    + (if col > 0 { interaction(t, left_type) } else { 0 })
}

pub open spec fn shift_spec(profile: int, new_val: int, n: int) -> int {
    profile / 3 + new_val * pow3(n - 1)
}

pub open spec fn max3(a: int, b: int, c: int) -> int {
    if a >= b && a >= c { a }
    else if b >= c { b }
    else { c }
}

pub open spec fn max_happiness(pos: int, ic: int, ec: int, profile: int, m: int, n: int) -> int
    decreases m * n - pos
{
    if pos >= m * n {
        0
    } else {
        let v_empty = max_happiness(pos + 1, ic, ec, shift_spec(profile, 0, n), m, n);
        let v_intro = if ic > 0 {
            delta_spec(1, pos, profile, m, n)
            + max_happiness(pos + 1, ic - 1, ec, shift_spec(profile, 1, n), m, n)
        } else {
            v_empty
        };
        let v_extro = if ec > 0 {
            delta_spec(2, pos, profile, m, n)
            + max_happiness(pos + 1, ic, ec - 1, shift_spec(profile, 2, n), m, n)
        } else {
            v_empty
        };
        max3(v_empty, v_intro, v_extro)
    }
}

proof fn pow3_positive(k: int)
    ensures pow3(k) > 0
    decreases k
{
    if k <= 0 {
    } else {
        pow3_positive(k - 1);
    }
}

proof fn pow3_monotone(k: int)
    requires k >= 0,
    ensures pow3(k) <= pow3(k + 1),
    decreases k
{
    pow3_positive(k);
}

proof fn pow3_bound_5(k: int)
    requires 0 <= k <= 5,
    ensures pow3(k) <= 243,
    decreases 5 - k
{
    reveal_with_fuel(pow3, 6);
    if k < 5 {
        pow3_bound_5(k + 1);
        pow3_monotone(k);
    }
}

proof fn shift_profile_valid(profile: int, n_val: int)
    requires
        n_val >= 1,
        0 <= profile < pow3(n_val),
    ensures
        pow3(n_val) == 3 * pow3(n_val - 1),
        pow3(n_val - 1) > 0,
        0 <= profile / 3 < pow3(n_val - 1),
        0 <= profile / 3 < pow3(n_val),
        0 <= profile / 3 + pow3(n_val - 1) < pow3(n_val),
        0 <= profile / 3 + 2 * pow3(n_val - 1) < pow3(n_val),
{
    pow3_positive(n_val - 1);
    pow3_positive(n_val);
}

proof fn max_happiness_bound(pos: int, ic: int, ec: int, profile: int, m: int, n: int)
    requires
        1 <= m <= 5,
        1 <= n <= 5,
        0 <= pos <= m * n,
        0 <= ic <= 6,
        0 <= ec <= 6,
        0 <= profile < pow3(n),
    ensures
        0 <= max_happiness(pos, ic, ec, profile, m, n) <= (ic + ec) * 120,
    decreases m * n - pos
{
    if pos >= m * n {
    } else {
        shift_profile_valid(profile, n);
        max_happiness_bound(pos + 1, ic, ec, shift_spec(profile, 0, n), m, n);
        if ic > 0 {
            max_happiness_bound(pos + 1, ic - 1, ec, shift_spec(profile, 1, n), m, n);
        }
        if ec > 0 {
            max_happiness_bound(pos + 1, ic, ec - 1, shift_spec(profile, 2, n), m, n);
        }
    }
}

pub open spec fn encode(pos: int, ic: int, ec: int, profile: int) -> int {
    ((pos * 7 + ic) * 7 + ec) * 243 + profile
}

proof fn radix_injective(a1: int, r1: int, a2: int, r2: int, base: int)
    requires
        base >= 1,
        0 <= r1 < base,
        0 <= r2 < base,
        a1 * base + r1 == a2 * base + r2,
    ensures a1 == a2, r1 == r2,
{
    if a1 < a2 {
        assert(a1 * base + r1 < (a1 + 1) * base) by (nonlinear_arith)
            requires r1 < base;
        assert((a1 + 1) * base <= a2 * base) by (nonlinear_arith)
            requires a1 + 1 <= a2, base >= 1;
        assert(a1 * base + r1 < a2 * base + r2);
    } else if a1 > a2 {
        assert(a2 * base + r2 < (a2 + 1) * base) by (nonlinear_arith)
            requires r2 < base;
        assert((a2 + 1) * base <= a1 * base) by (nonlinear_arith)
            requires a2 + 1 <= a1, base >= 1;
        assert(a2 * base + r2 < a1 * base + r1);
    }
}

proof fn encode_injective(pos1: int, ic1: int, ec1: int, profile1: int, pos2: int, ic2: int, ec2: int, profile2: int)
    requires
        0 <= ic1 < 7, 0 <= ec1 < 7, 0 <= profile1 < 243, pos1 >= 0,
        0 <= ic2 < 7, 0 <= ec2 < 7, 0 <= profile2 < 243, pos2 >= 0,
        encode(pos1, ic1, ec1, profile1) == encode(pos2, ic2, ec2, profile2),
    ensures pos1 == pos2, ic1 == ic2, ec1 == ec2, profile1 == profile2,
{
    let a1 = (pos1 * 7 + ic1) * 7 + ec1;
    let a2 = (pos2 * 7 + ic2) * 7 + ec2;
    assert(a1 * 243 + profile1 == encode(pos1, ic1, ec1, profile1));
    assert(a2 * 243 + profile2 == encode(pos2, ic2, ec2, profile2));
    radix_injective(a1, profile1, a2, profile2, 243);
    let b1 = pos1 * 7 + ic1;
    let b2 = pos2 * 7 + ic2;
    assert(b1 * 7 + ec1 == a1);
    assert(b2 * 7 + ec2 == a2);
    radix_injective(b1, ec1, b2, ec2, 7);
    radix_injective(pos1, ic1, pos2, ic2, 7);
}

proof fn encode_bound(pos: int, ic: int, ec: int, profile: int)
    requires
        0 <= pos <= 25,
        0 <= ic <= 6,
        0 <= ec <= 6,
        0 <= profile <= 242,
    ensures 0 <= encode(pos, ic, ec, profile) < 309_834,
{
    assert(0 <= (pos * 7 + ic) * 7 + ec <= 1273) by (nonlinear_arith)
        requires 0 <= pos <= 25, 0 <= ic <= 6, 0 <= ec <= 6;
}

pub open spec fn memo_ok(memo: Seq<i32>, m: int, n: int) -> bool {
    forall |p: int, i: int, e: int, pr: int|
        0 <= p <= m * n && 0 <= i <= 6 && 0 <= e <= 6 && 0 <= pr < pow3(n) ==>
        (#[trigger] memo[encode(p, i, e, pr)] != -1
            ==> memo[encode(p, i, e, pr)] as int == max_happiness(p, i, e, pr, m, n))
}

impl Solution {
    pub fn get_max_grid_happiness(m: i32, n: i32, introverts_count: i32, extroverts_count: i32) -> (result: i32)
        requires
            1 <= m <= 5,
            1 <= n <= 5,
            0 <= introverts_count <= 6,
            0 <= extroverts_count <= 6,
            introverts_count <= m * n,
            extroverts_count <= m * n,
        ensures
            result as int == max_happiness(0, introverts_count as int, extroverts_count as int, 0, m as int, n as int),
    {
        let mut pow3nm1: i32 = 1;
        let mut k: i32 = 1;
        proof {
            reveal_with_fuel(pow3, 6);
        }
        while k < n
            invariant
                1 <= k <= n,
                1 <= n <= 5,
                pow3nm1 as int == pow3((k - 1) as int),
                pow3nm1 >= 1,
                pow3nm1 <= 81,
            decreases n - k
        {
            proof {
                reveal_with_fuel(pow3, 6);
            }
            pow3nm1 = pow3nm1 * 3;
            k = k + 1;
        }
        proof {
            pow3_positive(n as int);
            pow3_positive((n - 1) as int);
            shift_profile_valid(0, n as int);
            pow3_bound_5(n as int);
        }
        let mut memo: Vec<i32> = Vec::new();
        let mut mi: usize = 0;
        while mi < 309_834
            invariant
                memo@.len() == mi as int,
                0 <= mi <= 309_834,
                forall |k: int| 0 <= k < mi as int ==> #[trigger] memo@[k] == -1,
            decreases 309_834 - mi,
        {
            memo.push(-1);
            mi = mi + 1;
        }
        proof {
            assert forall |p: int, i: int, e: int, pr: int|
                0 <= p <= m as int * n as int && 0 <= i <= 6 && 0 <= e <= 6 && 0 <= pr < pow3(n as int)
                && #[trigger] memo@[encode(p, i, e, pr)] != -1 implies
                memo@[encode(p, i, e, pr)] as int == max_happiness(p, i, e, pr, m as int, n as int) by {
                assert(m as int * n as int <= 25) by (nonlinear_arith)
                    requires 1 <= m <= 5, 1 <= n <= 5;
                encode_bound(p, i, e, pr);
            }
        }
        Solution::solve(m, n, 0, introverts_count, extroverts_count, 0, pow3nm1, &mut memo)
    }

    fn solve(m: i32, n: i32, pos: i32, ic: i32, ec: i32, profile: i32, pow3nm1: i32, memo: &mut Vec<i32>) -> (result: i32)
        requires
            1 <= m <= 5,
            1 <= n <= 5,
            0 <= pos <= m * n,
            0 <= ic <= 6,
            0 <= ec <= 6,
            0 <= profile < pow3(n as int),
            pow3(n as int) <= 243,
            pow3nm1 as int == pow3((n - 1) as int),
            1 <= pow3nm1 <= 81,
            old(memo)@.len() == 309_834,
            memo_ok(old(memo)@, m as int, n as int),
        ensures
            result as int == max_happiness(pos as int, ic as int, ec as int, profile as int, m as int, n as int),
            0 <= result <= (ic + ec) * 120,
            memo@.len() == 309_834,
            memo_ok(memo@, m as int, n as int),
        decreases m * n - pos
    {
        proof {
            assert(m * n <= 25) by (nonlinear_arith)
                requires 1 <= m <= 5, 1 <= n <= 5;
        }
        if pos >= m * n {
            return 0;
        }
        proof {
            encode_bound(pos as int, ic as int, ec as int, profile as int);
        }
        let idx: usize = (((pos * 7 + ic) * 7 + ec) * 243 + profile) as usize;
        let cached = memo[idx];
        if cached != -1 {
            proof {
                assert(memo@[idx as int] != -1);
                assert(idx as int == encode(pos as int, ic as int, ec as int, profile as int));
                assert(cached as int == max_happiness(pos as int, ic as int, ec as int, profile as int, m as int, n as int));
                max_happiness_bound(pos as int, ic as int, ec as int, profile as int, m as int, n as int);
            }
            return cached;
        }
        proof {
            shift_profile_valid(profile as int, n as int);
            max_happiness_bound(pos as int + 1, ic as int, ec as int, shift_spec(profile as int, 0, n as int), m as int, n as int);
            assert(0 <= profile / 3 < pow3nm1) by {
                assert(0 <= profile as int / 3 < pow3((n - 1) as int));
            };
        }
        let row = pos / n;
        let col = pos % n;
        let up_type = profile % 3;
        let left_type = (profile / pow3nm1) % 3;
        let shifted = profile / 3;
        let val_empty = Solution::solve(m, n, pos + 1, ic, ec, shifted, pow3nm1, memo);
        let mut best = val_empty;
        if ic > 0 {
            proof {
                max_happiness_bound(pos as int + 1, ic as int - 1, ec as int, shift_spec(profile as int, 1, n as int), m as int, n as int);
            }
            let base: i32 = 120;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -60 } else { -10 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -60 } else { -10 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + pow3nm1;
            let val_intro = d + Solution::solve(m, n, pos + 1, ic - 1, ec, next_pr, pow3nm1, memo);
            if val_intro > best {
                best = val_intro;
            }
        }
        if ec > 0 {
            proof {
                max_happiness_bound(pos as int + 1, ic as int, ec as int - 1, shift_spec(profile as int, 2, n as int), m as int, n as int);
            }
            let base: i32 = 40;
            let adj_up: i32 = if row > 0 {
                if up_type == 0 { 0 } else if up_type == 1 { -10 } else { 40 }
            } else { 0 };
            let adj_left: i32 = if col > 0 {
                if left_type == 0 { 0 } else if left_type == 1 { -10 } else { 40 }
            } else { 0 };
            let d = base + adj_up + adj_left;
            let next_pr = shifted + 2 * pow3nm1;
            let val_extro = d + Solution::solve(m, n, pos + 1, ic, ec - 1, next_pr, pow3nm1, memo);
            if val_extro > best {
                best = val_extro;
            }
        }
        proof {
            assert(idx as int == encode(pos as int, ic as int, ec as int, profile as int));
        }
        let ghost memo_before = memo@;
        memo.set(idx, best);
        proof {
            assert(memo@ =~= memo_before.update(idx as int, best));
            assert forall |p: int, i: int, e: int, pr: int|
                0 <= p <= m as int * n as int && 0 <= i <= 6 && 0 <= e <= 6 && 0 <= pr < pow3(n as int)
                && #[trigger] memo@[encode(p, i, e, pr)] != -1 implies
                memo@[encode(p, i, e, pr)] as int == max_happiness(p, i, e, pr, m as int, n as int) by {
                encode_bound(p, i, e, pr);
                assert(pr < 243);
                assert((profile as int) < 243);
                if p == pos as int && i == ic as int && e == ec as int && pr == profile as int {
                    assert(encode(p, i, e, pr) == idx as int);
                } else {
                    if encode(p, i, e, pr) == idx as int {
                        assert(encode(p, i, e, pr) == encode(pos as int, ic as int, ec as int, profile as int));
                        encode_injective(p, i, e, pr, pos as int, ic as int, ec as int, profile as int);
                    }
                    assert(encode(p, i, e, pr) != idx as int);
                    assert(memo@[encode(p, i, e, pr)] == memo_before[encode(p, i, e, pr)]);
                }
            }
        }
        best
    }
}

} 
