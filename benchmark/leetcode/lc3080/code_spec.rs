use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn best_in_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            nums.len() as int
        } else {
            let prev = Self::best_in_prefix(nums, marked, end - 1);
            let j = end - 1;
            if marked[j] {
                prev
            } else if prev == nums.len() as int || nums[j] < nums[prev] || (nums[j] == nums[prev] && j < prev) {
                j
            } else {
                prev
            }
        }
    }

    pub open spec fn best_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::best_in_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn sum_unmarked_prefix(nums: Seq<i32>, marked: Seq<bool>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_unmarked_prefix(nums, marked, end - 1)
                + if marked[end - 1] { 0 } else { nums[end - 1] as int }
        }
    }

    pub open spec fn sum_unmarked(nums: Seq<i32>, marked: Seq<bool>) -> int {
        Self::sum_unmarked_prefix(nums, marked, nums.len() as int)
    }

    pub open spec fn all_unmarked(n: int) -> Seq<bool>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            Self::all_unmarked(n - 1).push(false)
        }
    }

    pub open spec fn mark_index(marked: Seq<bool>, idx: int) -> Seq<bool> {
        if marked[idx] {
            marked
        } else {
            marked.update(idx, true)
        }
    }

    pub open spec fn mark_steps(nums: Seq<i32>, marked: Seq<bool>, steps: int) -> Seq<bool>
        decreases steps,
    {
        if steps <= 0 {
            marked
        } else {
            let prev = Self::mark_steps(nums, marked, steps - 1);
            let b = Self::best_unmarked(nums, prev);
            if b == nums.len() as int {
                prev
            } else {
                prev.update(b, true)
            }
        }
    }

    pub open spec fn apply_query(nums: Seq<i32>, marked: Seq<bool>, query: Vec<i32>) -> Seq<bool> {
        let marked1 = Self::mark_index(marked, query[0] as int);
        Self::mark_steps(nums, marked1, query[1] as int)
    }

    pub open spec fn state_after(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<bool>
        decreases t,
    {
        if t <= 0 {
            Self::all_unmarked(nums.len() as int)
        } else {
            let prev = Self::state_after(nums, queries, t - 1);
            Self::apply_query(nums, prev, queries[t - 1])
        }
    }

    pub open spec fn answers_prefix(nums: Seq<i32>, queries: Seq<Vec<i32>>, t: int) -> Seq<i64>
        decreases t,
    {
        if t <= 0 {
            seq![]
        } else {
            let prev = Self::answers_prefix(nums, queries, t - 1);
            let marks = Self::state_after(nums, queries, t);
            prev.push(Self::sum_unmarked(nums, marks) as i64)
        }
    }
}

pub open spec fn encode(v: int, i: int) -> int {
    v * 200000 + i
}

pub open spec fn decode_idx(e: int) -> int {
    e % 200000
}

pub open spec fn sorted_asc(s: Seq<int>) -> bool {
    forall|a: int, b: int| 0 <= a <= b < s.len() ==> s[a] <= s[b]
}

pub open spec fn merge_seq(a: Seq<int>, b: Seq<int>) -> Seq<int>
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else if a[0] <= b[0] {
        seq![a[0]] + merge_seq(a.drop_first(), b)
    } else {
        seq![b[0]] + merge_seq(a, b.drop_first())
    }
}

pub open spec fn merge_sort_seq(s: Seq<int>) -> Seq<int>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let mid = s.len() as int / 2;
        merge_seq(merge_sort_seq(s.subrange(0, mid)), merge_sort_seq(s.subrange(mid, s.len() as int)))
    }
}

pub open spec fn to_int_seq64(s: Seq<i64>) -> Seq<int> {
    s.map_values(|x: i64| x as int)
}

fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
    requires
        sorted_asc(to_int_seq64(a@)),
        sorted_asc(to_int_seq64(b@)),
    ensures
        to_int_seq64(result@) == merge_seq(to_int_seq64(a@), to_int_seq64(b@)),
{
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec(v: &Vec<i64>) -> (result: Vec<i64>)
    requires v.len() <= 100_000,
    ensures to_int_seq64(result@) == merge_sort_seq(to_int_seq64(v@)),
    decreases v.len()
{
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len() {
            right.push(v[i2]);
            i2 += 1;
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        let result = merge_exec(&sorted_left, &sorted_right);
        result
    }
}

fn encode_exec(v: i32, i: usize) -> (result: i64)
    requires 1 <= v <= 100000, i < 100000,
    ensures result as int == encode(v as int, i as int),
{
    (v as i64) * 200000 + (i as i64)
}

fn decode_idx_exec(e: i64) -> (result: i64)
    requires 0 <= e <= 100000i64 * 200000i64 + 199999i64,
    ensures result as int == decode_idx(e as int),
{
    e % 200000
}

impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (result: Vec<i64>)
        requires
            1 <= queries.len() <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] queries[i].len() == 2,
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][0] < nums.len(),
            forall |i: int| 0 <= i < queries.len() && queries[i].len() == 2 ==> 0 <= #[trigger] queries[i][1] <= nums.len() - 1,
        ensures
            result@ == Self::answers_prefix(nums@, queries@, queries.len() as int),
    {
        let n = nums.len();

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n {
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }
        let sorted = merge_sort_exec(&enc);

        let mut marked: Vec<bool> = Vec::new();
        let mut jj: usize = 0;
        while jj < n {
            marked.push(false);
            jj += 1;
        }

        let mut total: i64 = 0;
        let mut pp: usize = 0;
        while pp < n {
            total = total + nums[pp] as i64;
            pp += 1;
        }
        let mut unmarked_sum: i64 = total;

        let mut ptr: usize = 0;
        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let idx = queries[q][0] as usize;
            let k = queries[q][1];
            if !marked[idx] {
                marked.set(idx, true);
                unmarked_sum = unmarked_sum - nums[idx] as i64;
            }

            let mut t: i32 = 0;
            while t < k && ptr < n {
                let mut cont: bool = false;
                if ptr < n {
                    let sp = sorted[ptr];
                    let di = decode_idx_exec(sp);
                    cont = marked[di as usize];
                }
                while cont {
                    ptr += 1;
                    cont = false;
                    if ptr < n {
                        let sp = sorted[ptr];
                        let di = decode_idx_exec(sp);
                        cont = marked[di as usize];
                    }
                }
                if ptr < n {
                    let sp2 = sorted[ptr];
                    let di2 = decode_idx_exec(sp2);
                    let target = di2 as usize;
                    marked.set(target, true);
                    unmarked_sum = unmarked_sum - nums[target] as i64;
                    ptr += 1;
                }
                t += 1;
            }

            result.push(unmarked_sum);
            q += 1;
        }

        result
    }
}

}
