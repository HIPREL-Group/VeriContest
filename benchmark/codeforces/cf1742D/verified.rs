use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_gcd(a: nat, b: nat) -> nat
        decreases b
    {
        if b == 0 { a } else { Self::spec_gcd(b, a % b) }
    }

    pub open spec fn spec_divides_both(d: int, x: int, y: int) -> bool {
        x % d == 0 && y % d == 0
    }

    pub open spec fn spec_coprime_values(x: int, y: int) -> bool {
        x >= 1 && y >= 1 && Self::spec_gcd(x as nat, y as nat) == 1
    }

    pub open spec fn spec_last_pos_prefix(a: Seq<i32>, v: int, i: int) -> int
        decreases i
    {
        if i <= 0 {
            -1
        } else {
            let prev = Self::spec_last_pos_prefix(a, v, i - 1);
            if a[i - 1] as int == v {
                i
            } else {
                prev
            }
        }
    }

    pub open spec fn spec_last_pos(a: Seq<i32>, v: int) -> int {
        Self::spec_last_pos_prefix(a, v, a.len() as int)
    }

    pub open spec fn spec_pair_score(a: Seq<i32>, x: int, y: int) -> int {
        let px = Self::spec_last_pos(a, x);
        let py = Self::spec_last_pos(a, y);
        if px >= 1 && py >= 1 && Self::spec_coprime_values(x, y) {
            px + py
        } else {
            -1
        }
    }

    pub open spec fn spec_optimal_answer(a: Seq<i32>, res: int) -> bool {
        &&& forall|x: int, y: int|
            1 <= x <= 1000 && 1 <= y <= 1000 ==> Self::spec_pair_score(a, x, y) <= res
        &&& (res == -1 || exists|x: int, y: int|
            1 <= x <= 1000 && 1 <= y <= 1000 && Self::spec_pair_score(a, x, y) == res)
    }

    pub fn is_coprime_values(x: i32, y: i32) -> (res: bool)
        requires
            1 <= x <= 1000,
            1 <= y <= 1000,
        ensures
            res == Self::spec_coprime_values(x as int, y as int),
    {
        let ghost sx = x as nat;
        let ghost sy = y as nat;
        let mut a = x;
        let mut b = y;
        while b != 0
            invariant
                1 <= a <= 1000,
                0 <= b <= 1000,
                Self::spec_gcd(a as nat, b as nat) == Self::spec_gcd(sx, sy),
            decreases b as int,
        {
            let prev_a = a;
            let prev_b = b;
            proof {
                assert(Self::spec_gcd(prev_a as nat, prev_b as nat)
                    == Self::spec_gcd(prev_b as nat, (prev_a % prev_b) as nat));
            }
            let r = a % b;
            a = b;
            b = r;
        }
        proof {
            assert(b == 0);
            assert(Self::spec_gcd(a as nat, 0) == a as nat);
            assert(a as nat == Self::spec_gcd(sx, sy));
            assert((a == 1) == (Self::spec_gcd(sx, sy) == 1));
            assert(Self::spec_coprime_values(x as int, y as int) == (Self::spec_gcd(sx, sy) == 1));
        }
        a == 1
    }

    pub fn max_coprime_index_sum(a: Vec<i32>) -> (res: i32)
        requires
            2 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1000,
        ensures
            Self::spec_optimal_answer(a@, res as int),
    {
        let n = a.len();
        let mut last: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001
            invariant
                0 <= k <= 1001,
                last.len() == k,
                forall|j: int| 0 <= j < k as int ==> last[j] == -1,
            decreases 1001 - k,
        {
            last.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                2 <= n <= 200000,
                0 <= i <= n,
                last.len() == 1001,
                forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1000,
                forall|v: int| 1 <= v <= 1000 ==> last[v] as int == Self::spec_last_pos_prefix(a@, v, i as int),
                forall|v: int| 1 <= v <= 1000 ==> last[v] == -1 || (1 <= last[v] <= i as i32),
                last[0] == -1,
            decreases n - i,
        {
            let v = a[i] as usize;
            let ghost last_prev = last@;
            assert(i < n);
            assert(i <= 199999);
            last.set(v, i as i32 + 1);
            proof {
                assert(v as int == a[i as int] as int);
                assert(1 <= v as int <= 1000);
                assert forall|vv: int| 1 <= vv <= 1000 implies last[vv] as int == Self::spec_last_pos_prefix(a@, vv, i as int + 1) by {
                    if vv == v as int {
                        assert(a[i as int] as int == vv);
                        assert(Self::spec_last_pos_prefix(a@, vv, i as int + 1) == i as int + 1);
                        assert(last[vv] as int == i as int + 1);
                    } else {
                        assert(last[vv] == last_prev[vv]);
                        assert(last_prev[vv] as int == Self::spec_last_pos_prefix(a@, vv, i as int));
                        assert(a[i as int] as int != vv);
                        assert(Self::spec_last_pos_prefix(a@, vv, i as int + 1) == Self::spec_last_pos_prefix(a@, vv, i as int));
                    }
                };
                assert forall|vv: int| 1 <= vv <= 1000 implies last[vv] == -1 || (1 <= last[vv] <= i as i32 + 1) by {
                    if vv == v as int {
                        assert(last[vv] == i as i32 + 1);
                    } else {
                        assert(last[vv] == last_prev[vv]);
                    }
                };
                assert(last[0] == -1);
            }
            i = i + 1;
        }

        let mut ans: i32 = -1;
        let mut x: i32 = 1;
        while x <= 1000
            invariant
                a.len() == n,
                2 <= n <= 200000,
                last.len() == 1001,
                forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1000,
                forall|v: int| 1 <= v <= 1000 ==> last[v] as int == Self::spec_last_pos(a@, v),
                forall|v: int| 1 <= v <= 1000 ==> last[v] == -1 || (1 <= last[v] <= n as i32),
                1 <= x <= 1001,
                ans >= -1,
                forall|vx: int, vy: int|
                    1 <= vx < x as int && 1 <= vy <= 1000 ==> Self::spec_pair_score(a@, vx, vy) <= ans as int,
                ans == -1 || exists|wx: int, wy: int|
                    1 <= wx < x as int && 1 <= wy <= 1000 && Self::spec_pair_score(a@, wx, wy) == ans as int,
            decreases 1001 - x,
        {
            let mut y: i32 = 1;
            while y <= 1000
                invariant
                    a.len() == n,
                    2 <= n <= 200000,
                    last.len() == 1001,
                    forall|j: int| 0 <= j < a.len() as int ==> 1 <= #[trigger] a[j] <= 1000,
                    forall|v: int| 1 <= v <= 1000 ==> last[v] as int == Self::spec_last_pos(a@, v),
                    forall|v: int| 1 <= v <= 1000 ==> last[v] == -1 || (1 <= last[v] <= n as i32),
                    1 <= x <= 1000,
                    1 <= y <= 1001,
                    ans >= -1,
                    forall|vx: int, vy: int|
                        1 <= vx < x as int && 1 <= vy <= 1000 ==> Self::spec_pair_score(a@, vx, vy) <= ans as int,
                    forall|vy: int| 1 <= vy < y as int ==> Self::spec_pair_score(a@, x as int, vy) <= ans as int,
                    ans == -1 || exists|wx: int, wy: int|
                        ((1 <= wx < x as int && 1 <= wy <= 1000)
                            || (wx == x as int && 1 <= wy < y as int))
                        && Self::spec_pair_score(a@, wx, wy) == ans as int,
                decreases 1001 - y,
            {
                let old_ans = ans;
                let cop = Self::is_coprime_values(x, y);
                let lx = last[x as usize];
                let ly = last[y as usize];
                if lx != -1 && ly != -1 && cop {
                    proof {
                        assert(1 <= x as int <= 1000);
                        assert(1 <= y as int <= 1000);
                        assert(lx == last[x as int]);
                        assert(ly == last[y as int]);
                        assert(1 <= lx <= n as i32);
                        assert(1 <= ly <= n as i32);
                    }
                    let cand = lx + ly;
                    if cand > ans {
                        ans = cand;
                    }
                    proof {
                        assert(cop == Self::spec_coprime_values(x as int, y as int));
                        assert(lx as int == Self::spec_last_pos(a@, x as int));
                        assert(ly as int == Self::spec_last_pos(a@, y as int));
                        assert(lx >= 1);
                        assert(ly >= 1);
                        assert(cand as int == Self::spec_pair_score(a@, x as int, y as int));
                        assert(old_ans <= ans);
                        assert(cand <= ans);
                        assert(Self::spec_pair_score(a@, x as int, y as int) <= ans as int);
                    }
                } else {
                    proof {
                        assert(cop == Self::spec_coprime_values(x as int, y as int));
                        if lx == -1 {
                            assert(Self::spec_pair_score(a@, x as int, y as int) == -1);
                        } else if ly == -1 {
                            assert(Self::spec_pair_score(a@, x as int, y as int) == -1);
                        } else {
                            assert(!cop);
                            assert(!Self::spec_coprime_values(x as int, y as int));
                            assert(Self::spec_pair_score(a@, x as int, y as int) == -1);
                        }
                        assert(ans == old_ans);
                    }
                }
                proof {
                    assert(old_ans <= ans);
                    assert forall|vx: int, vy: int|
                        1 <= vx < x as int && 1 <= vy <= 1000 implies Self::spec_pair_score(a@, vx, vy) <= ans as int by {
                        assert(Self::spec_pair_score(a@, vx, vy) <= old_ans as int);
                    };
                    assert forall|vy: int| 1 <= vy < y as int implies Self::spec_pair_score(a@, x as int, vy) <= ans as int by {
                        assert(Self::spec_pair_score(a@, x as int, vy) <= old_ans as int);
                    };
                    assert(Self::spec_pair_score(a@, x as int, y as int) <= ans as int);
                    assert forall|vy: int| 1 <= vy < y as int + 1 implies Self::spec_pair_score(a@, x as int, vy) <= ans as int by {
                        if vy < y as int {
                            assert(Self::spec_pair_score(a@, x as int, vy) <= ans as int);
                        } else {
                            assert(vy == y as int);
                            assert(Self::spec_pair_score(a@, x as int, vy) <= ans as int);
                        }
                    };

                    if ans == -1 {
                    } else if ans == old_ans {
                        assert(old_ans != -1);
                        assert(exists|wx: int, wy: int|
                            ((1 <= wx < x as int && 1 <= wy <= 1000)
                                || (wx == x as int && 1 <= wy < y as int))
                            && Self::spec_pair_score(a@, wx, wy) == old_ans as int);
                        let ex = choose|wx: int, wy: int|
                            ((1 <= wx < x as int && 1 <= wy <= 1000)
                                || (wx == x as int && 1 <= wy < y as int))
                            && Self::spec_pair_score(a@, wx, wy) == old_ans as int;
                        assert(((1 <= ex.0 < x as int && 1 <= ex.1 <= 1000)
                            || (ex.0 == x as int && 1 <= ex.1 < y as int + 1))
                            && Self::spec_pair_score(a@, ex.0, ex.1) == ans as int);
                    } else {
                        assert(ans != old_ans);
                        assert(lx != -1 && ly != -1 && cop);
                        assert(cop == Self::spec_coprime_values(x as int, y as int));
                        assert(lx as int == Self::spec_last_pos(a@, x as int));
                        assert(ly as int == Self::spec_last_pos(a@, y as int));
                        assert(Self::spec_pair_score(a@, x as int, y as int) == ans as int);
                        assert(1 <= y as int && (y as int) < (y as int) + 1);
                        assert((x as int == x as int && 1 <= y as int && (y as int) < (y as int) + 1)
                            && Self::spec_pair_score(a@, x as int, y as int) == ans as int);
                    }
                }
                y = y + 1;
            }
            proof {
                assert(y == 1001);
                assert forall|vx: int, vy: int|
                    1 <= vx < x as int + 1 && 1 <= vy <= 1000 implies Self::spec_pair_score(a@, vx, vy) <= ans as int by {
                    if vx < x as int {
                        assert(Self::spec_pair_score(a@, vx, vy) <= ans as int);
                    } else {
                        assert(vx == x as int);
                        assert(1 <= vy < y as int);
                        assert(Self::spec_pair_score(a@, x as int, vy) <= ans as int);
                    }
                };

                if ans == -1 {
                } else {
                    assert(exists|wx: int, wy: int|
                        ((1 <= wx < x as int && 1 <= wy <= 1000)
                            || (wx == x as int && 1 <= wy < y as int))
                        && Self::spec_pair_score(a@, wx, wy) == ans as int);
                    let ex = choose|wx: int, wy: int|
                        ((1 <= wx < x as int && 1 <= wy <= 1000)
                            || (wx == x as int && 1 <= wy < y as int))
                        && Self::spec_pair_score(a@, wx, wy) == ans as int;
                    assert(1 <= ex.0 < x as int + 1);
                    assert(1 <= ex.1 <= 1000);
                }
            }
            x = x + 1;
        }

        proof {
            assert(x == 1001);
            assert forall|vx: int, vy: int|
                1 <= vx <= 1000 && 1 <= vy <= 1000
                    implies Self::spec_pair_score(a@, vx, vy) <= ans as int by {
                assert(1 <= vx < x as int);
                assert(Self::spec_pair_score(a@, vx, vy) <= ans as int);
            };
            if ans != -1 {
                let ex = choose|wx: int, wy: int|
                    1 <= wx < x as int && 1 <= wy <= 1000 && Self::spec_pair_score(a@, wx, wy) == ans as int;
                let wx = ex.0;
                let wy = ex.1;
                assert(1 <= wx <= 1000);
                assert(1 <= wy <= 1000);
                assert(Self::spec_pair_score(a@, wx, wy) == ans as int);
            }
            assert(Self::spec_optimal_answer(a@, ans as int));
        }
        ans
    }
}

}
