use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub open spec fn index_of(v: i32, s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            -1int
        } else if s[0] == v {
            0int
        } else {
            let r = Self::index_of(v, s.subrange(1, s.len() as int));
            if r == -1 { -1int } else { 1 + r }
        }
    }

    pub open spec fn rank(v: i32, arr2: Seq<i32>) -> int {
        let idx = Self::index_of(v, arr2);
        if idx >= 0 {
            idx
        } else {
            arr2.len() + v as int
        }
    }

    pub fn relative_sort_array(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr1@.len() <= 1000,
            1 <= arr2@.len() <= 1000,
            forall |i: int| 0 <= i < arr1@.len() ==> 0 <= #[trigger] arr1@[i] <= 1000,
            forall |i: int| 0 <= i < arr2@.len() ==> 0 <= #[trigger] arr2@[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < arr2@.len() ==> arr2@[i] != arr2@[j],
            forall |i: int| 0 <= i < arr2@.len() ==>
                Self::count(arr1@, arr2@[i]) >= 1,
        ensures
            result@.len() == arr1@.len(),
            forall |v: i32| Self::count(result@, v) == Self::count(arr1@, v),
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) < 0
                && Self::index_of(result@[j], arr2@) >= 0
                ==> false,
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) >= 0
                && Self::index_of(result@[j], arr2@) >= 0
                ==> Self::index_of(result@[i], arr2@) <= Self::index_of(result@[j], arr2@),
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) < 0
                && Self::index_of(result@[j], arr2@) < 0
                ==> result@[i] <= result@[j],
    {
        let mut cnt: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < 1001 {
            cnt.push(0);
            i = i + 1;
        }

        let mut j: usize = 0;
        while j < arr1.len() {
            let v = arr1[j] as usize;
            cnt.set(v, cnt[v] + 1);
            j = j + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < arr2.len() {
            let v = arr2[k];
            while cnt[v as usize] > 0 {
                result.push(v);
                cnt.set(v as usize, cnt[v as usize] - 1);
            }
            k = k + 1;
        }

        let mut m: usize = 0;
        while m < 1001 {
            while cnt[m] > 0 {
                result.push(m as i32);
                cnt.set(m, cnt[m] - 1);
            }
            m = m + 1;
        }

        result
    }
}

}
