use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn i32_min() -> int {
        -2147483648
    }

    pub open spec fn i32_max() -> int {
        2147483647
    }

    pub open spec fn checked_add_i32_or(a: int, b: int, fallback: int) -> int {
        let s = a + b;
        if Self::i32_min() <= s <= Self::i32_max() { s } else { fallback }
    }

    pub open spec fn color_at(colors: Seq<i32>, idx: int) -> int {
        if colors.len() == 0 { 0 } else { colors[idx % (colors.len() as int)] as int }
    }

    pub open spec fn cnt_after(colors: Seq<i32>, k: int, i: int) -> int
        decreases if i > 0 { i } else { 0 },
    {
        if i <= 0 {
            1
        } else {
            let prev = Self::cnt_after(colors, k, i - 1);
            if Self::color_at(colors, i) != Self::color_at(colors, i - 1) {
                if prev < k { prev + 1 } else { k }
            } else {
                1
            }
        }
    }

    pub open spec fn ans_after(colors: Seq<i32>, k: int, i: int) -> int
        decreases if i > 0 { i } else { 0 },
    {
        if i <= 0 {
            0
        } else {
            let prev = Self::ans_after(colors, k, i - 1);
            let c = Self::cnt_after(colors, k, i);
            if c >= k {
                Self::checked_add_i32_or(prev, 1, prev)
            } else {
                prev
            }
        }
    }

    pub open spec fn number_of_alternating_groups_spec(colors: Seq<i32>, k: int, result: int) -> bool {
        &&& 3 <= colors.len() <= 100000
        &&& 3 <= k <= colors.len()
        &&& forall |i: int| 0 <= i < colors.len() ==> (#[trigger] colors[i] == 0 || colors[i] == 1)
        &&& result == Self::ans_after(colors, k, colors.len() + k - 2)
    }

    pub fn number_of_alternating_groups(colors: Vec<i32>, k: i32) -> (result: i32)
        requires
            3 <= colors.len() <= 100000,
            3 <= k <= colors.len(),
            forall |i: int| 0 <= i < colors.len() ==> (#[trigger] colors[i] == 0 || colors[i] == 1),
        ensures
            Self::number_of_alternating_groups_spec(colors@, k as int, result as int),
    {
        let n = colors.len();
        let ku = k as usize;
        let mut ans = 0i32;
        let mut cnt = 1usize;
        let mut i = 1usize;
        while i < n + ku - 1
            invariant
                n == colors.len(),
                3 <= n <= 100000,
                3 <= ku <= n,
                1 <= i <= n + ku - 1,
                cnt >= 1,
                ans >= 0,
                cnt as int == Self::cnt_after(colors@, ku as int, i as int - 1),
                ans as int == Self::ans_after(colors@, ku as int, i as int - 1),
            decreases n + ku - 1 - i,
        {
            assert(i < n + ku - 1);
            let cur = i % n;
            let prev = (i - 1) % n;
            if colors[cur] != colors[prev] {
                cnt = if cnt < ku { cnt + 1 } else { ku };
            } else {
                cnt = 1;
            }
            assert(Self::cnt_after(colors@, ku as int, i as int) == cnt as int);
            if cnt >= ku {
                let old_ans = ans;
                ans = ans.checked_add(1).unwrap_or(ans);
                assert(ans as int == Self::checked_add_i32_or(old_ans as int, 1, old_ans as int));
            } else {
                assert(Self::ans_after(colors@, ku as int, i as int) == Self::ans_after(colors@, ku as int, i as int - 1));
            }
            assert(ans as int == Self::ans_after(colors@, ku as int, i as int));
            i += 1;
        }
        assert(ans as int == Self::ans_after(colors@, ku as int, n as int + ku as int - 2));
        ans
    }
}

}
