use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn freq_at(requests: Seq<Vec<i32>>, idx: int, k: int) -> int
        decreases requests.len() - k
    {
        if k >= requests.len() as int {
            0
        } else {
            (if requests[k]@[0] as int <= idx && idx <= requests[k]@[1] as int {
                1int
            } else {
                0int
            }) + Self::freq_at(requests, idx, k + 1)
        }
    }

    pub open spec fn freq_vec(requests: Seq<Vec<i32>>, n: int) -> Seq<int> {
        Seq::new(n as nat, |i: int| Self::freq_at(requests, i, 0))
    }

    pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn dot_product_int(a: Seq<int>, b: Seq<int>, k: int) -> int
        decreases a.len() - k
    {
        if k >= a.len() as int {
            0
        } else {
            a[k] * b[k] + Self::dot_product_int(a, b, k + 1)
        }
    }

    pub open spec fn is_sorted_int(s: Seq<int>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_int(s: Seq<int>, v: int) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s.last() == v { 1int } else { 0int })
                + Self::count_int(s.drop_last(), v)
        }
    }

    pub open spec fn is_perm_int(a: Seq<int>, b: Seq<int>) -> bool {
        a.len() == b.len()
            && forall |v: int| Self::count_int(a, v) == Self::count_int(b, v)
    }

    pub open spec fn to_int_seq_i64(s: Seq<i64>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len()
            && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ_i64(s: Seq<i64>, val: i64) -> int
        decreases s.len()
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ_i64(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm_i64(a: Seq<i64>, b: Seq<i64>) -> bool {
        a.len() == b.len()
            && forall |v: i64| Self::count_occ_i64(a, v) == Self::count_occ_i64(b, v)
    }

    pub open spec fn is_sorted_i64(s: Seq<i64>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort(input: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted(result@),
            result@.len() == input@.len(),
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    fn ms_merge_i64(a: &Vec<i64>, b: &Vec<i64>) -> (result: Vec<i64>)
        requires Self::is_sorted_i64(a@), Self::is_sorted_i64(b@)
        ensures
            Self::is_sorted_i64(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm_i64(result@, a@ + b@),
    {
        let mut result: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort_i64(input: &Vec<i64>) -> (result: Vec<i64>)
        ensures
            Self::is_sorted_i64(result@),
            result@.len() == input@.len(),
            Self::is_perm_i64(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort_i64(&left);
        let sorted_right = Self::ms_sort_i64(&right);
        let result = Self::ms_merge_i64(&sorted_left, &sorted_right);
        result
    }

    pub fn max_sum_range_query(nums: Vec<i32>, requests: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= nums@.len() <= 100_000,
            forall |i: int| 0 <= i < nums@.len() ==>
                0 <= #[trigger] nums@[i] <= 100_000,
            1 <= requests@.len() <= 100_000,
            forall |i: int| 0 <= i < requests@.len() ==> (
                (#[trigger] requests@[i])@.len() == 2
                    && 0 <= requests@[i]@[0]
                    && requests@[i]@[0] <= requests@[i]@[1]
                    && (requests@[i]@[1] as int) < nums@.len() as int
            ),
        ensures
            0 <= result < 1_000_000_007,
            exists |sv: Seq<int>, sf: Seq<int>|
                sv.len() == nums@.len()
                && sf.len() == nums@.len()
                && Self::is_sorted_int(sv)
                && Self::is_sorted_int(sf)
                && Self::is_perm_int(sv, Self::to_int_seq(nums@))
                && Self::is_perm_int(sf, Self::freq_vec(requests@, nums@.len() as int))
                && result as int
                    == Self::dot_product_int(sv, sf, 0) % 1_000_000_007
                && forall |c: Seq<int>|
                    c.len() == sv.len() && Self::is_perm_int(c, sv)
                        ==> Self::dot_product_int(sv, sf, 0)
                            >= Self::dot_product_int(c, sf, 0),
    {
        let n = nums.len();
        let m = requests.len();
        let modval: i64 = 1_000_000_007;
        let mut count: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut freq: i64 = 0;
            let mut r: usize = 0;
            while r < m {
                if requests[r][0] as usize <= i && i <= requests[r][1] as usize {
                    freq = freq + 1;
                }
                r = r + 1;
            }
            count.push(freq);
            i = i + 1;
        }
        let nums = Self::ms_sort(&nums);
        let sorted_count = Self::ms_sort_i64(&count);
        let mut result: i64 = 0;
        let mut k: usize = 0;
        while k < n {
            result = (result + nums[k] as i64 * sorted_count[k]) % modval;
            k = k + 1;
        }
        result as i32
    }
}

}
