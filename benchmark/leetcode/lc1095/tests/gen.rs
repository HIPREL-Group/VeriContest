use vstd::prelude::*;

verus! {

pub struct MountainArray {
    pub data: Vec<i32>,
}

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 { 0 }
        else { Self::sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
    }

    proof fn lemma_sum_mono(deltas: Seq<i32>, a: int, b: int)
        requires
            0 <= a <= b <= deltas.len(),
            forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
        ensures
            Self::sum_deltas(deltas, a) <= Self::sum_deltas(deltas, b),
        decreases b - a,
    {
        if a < b {
            Self::lemma_sum_mono(deltas, a, b - 1);
        }
    }

    proof fn lemma_sum_strict(deltas: Seq<i32>, a: int, b: int)
        requires
            0 <= a < b <= deltas.len(),
            forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
        ensures
            Self::sum_deltas(deltas, a) + (b - a) <= Self::sum_deltas(deltas, b),
        decreases b - a,
    {
        if b - a > 1 {
            Self::lemma_sum_strict(deltas, a, b - 1);
        }
    }

    proof fn lemma_sum_nonneg(deltas: Seq<i32>, end: int)
        requires
            0 <= end <= deltas.len(),
            forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
        ensures
            Self::sum_deltas(deltas, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_sum_nonneg(deltas, end - 1);
        }
    }

    pub fn generate_test_case(
        asc_deltas: &Vec<i32>,
        desc_deltas: &Vec<i32>,
        base: i32,
        target: i32,
        mutation_kind: u8,
    ) -> (result: (i32, MountainArray))
        requires
            asc_deltas.len() >= 1,
            desc_deltas.len() >= 1,
            asc_deltas.len() + desc_deltas.len() + 1 >= 3,
            asc_deltas.len() + desc_deltas.len() + 1 <= 10_000,
            0 <= base,
            forall|i: int| 0 <= i < asc_deltas.len() ==> 1 <= #[trigger] asc_deltas[i],
            forall|i: int| 0 <= i < desc_deltas.len() ==> 1 <= #[trigger] desc_deltas[i],
            base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int) <= 1_000_000_000,
            Self::sum_deltas(desc_deltas@, desc_deltas.len() as int)
                <= base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int),
            0 <= target <= 1_000_000_000,
        ensures
            0 <= result.0 <= 1_000_000_000,
            3 <= result.1.data.len() <= 10_000,
            forall |i: int| 0 <= i < result.1.data.len() ==> 0 <= #[trigger] result.1.data@[i] <= 1_000_000_000,
            exists |peak: int| Self::is_mountain(result.1.data@, peak),
    {
        let total_len: usize = asc_deltas.len() + desc_deltas.len() + 1;
        let peak_pos: usize = asc_deltas.len();

        let mut arr: Vec<i32> = Vec::new();

        proof {
            Self::lemma_sum_nonneg(asc_deltas@, asc_deltas.len() as int);
            assert(base <= 1_000_000_000) by {
                assert(base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int) <= 1_000_000_000);
                assert(Self::sum_deltas(asc_deltas@, asc_deltas.len() as int) >= 0);
            };
        }

        arr.push(base);

        // Build ascending part: arr[k] = base + sum_deltas(asc_deltas, k)
        let mut i: usize = 0;
        while i < asc_deltas.len()
            invariant
                0 <= i <= asc_deltas.len(),
                arr.len() == i + 1,
                asc_deltas.len() >= 1,
                desc_deltas.len() >= 1,
                total_len == asc_deltas.len() + desc_deltas.len() + 1,
                peak_pos == asc_deltas.len(),
                0 <= base,
                base <= 1_000_000_000,
                forall|k: int| 0 <= k < asc_deltas.len() ==> #[trigger] asc_deltas[k] >= 1i32,
                base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int) <= 1_000_000_000,
                forall|k: int| 0 <= k <= i as int ==>
                    #[trigger] arr[k] as int == base as int + Self::sum_deltas(asc_deltas@, k),
                forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 1_000_000_000,
                forall|k: int, l: int| 0 <= k < l < arr.len() ==> arr[k] < arr[l],
            decreases asc_deltas.len() - i,
        {
            proof {
                Self::lemma_sum_mono(asc_deltas@, (i + 1) as int, asc_deltas.len() as int);
                Self::lemma_sum_nonneg(asc_deltas@, (i + 1) as int);
            }

            let next = arr[i] + asc_deltas[i];

            proof {
                assert(next as int == base as int + Self::sum_deltas(asc_deltas@, (i + 1) as int));

                assert forall|k: int| 0 <= k < arr.len() implies arr[k] < next by {
                    assert(arr[k] as int == base as int + Self::sum_deltas(asc_deltas@, k));
                    assert(next as int == base as int + Self::sum_deltas(asc_deltas@, (i + 1) as int));
                    Self::lemma_sum_strict(asc_deltas@, k, (i + 1) as int);
                };
            }

            arr.push(next);
            i = i + 1;

            proof {
                assert forall|k: int, l: int| 0 <= k < l < arr.len() implies arr[k] < arr[l] by {
                    if l < (arr.len() - 1) as int {
                    } else {
                        assert(arr[l] == next);
                    }
                };
            }
        }

        // arr now has peak_pos + 1 elements, arr[peak_pos] is the peak
        let peak_val = arr[peak_pos];

        proof {
            assert(peak_val as int == base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int));
        }

        // Build descending part: arr[peak_pos + j] = peak_val - sum_deltas(desc_deltas, j)
        let mut j: usize = 0;
        while j < desc_deltas.len()
            invariant
                0 <= j <= desc_deltas.len(),
                arr.len() == peak_pos + 1 + j,
                peak_pos == asc_deltas.len(),
                asc_deltas.len() >= 1,
                desc_deltas.len() >= 1,
                total_len == asc_deltas.len() + desc_deltas.len() + 1,
                0 <= base,
                peak_val as int == base as int + Self::sum_deltas(asc_deltas@, asc_deltas.len() as int),
                peak_val <= 1_000_000_000,
                forall|k: int| 0 <= k < desc_deltas.len() ==> #[trigger] desc_deltas[k] >= 1i32,
                Self::sum_deltas(desc_deltas@, desc_deltas.len() as int) <= peak_val as int,
                // Ascending part unchanged
                forall|k: int| 0 <= k < asc_deltas.len() ==> #[trigger] asc_deltas[k] >= 1i32,
                forall|k: int| 0 <= k <= peak_pos as int ==>
                    #[trigger] arr[k] as int == base as int + Self::sum_deltas(asc_deltas@, k),
                forall|k: int, l: int| 0 <= k < l <= peak_pos as int ==> arr[k] < arr[l],
                // Descending part
                forall|k: int| 0 <= k <= j as int ==>
                    #[trigger] arr[peak_pos as int + k] as int == peak_val as int - Self::sum_deltas(desc_deltas@, k),
                forall|k: int, l: int| peak_pos as int <= k < l < arr.len() ==> arr[k] > arr[l],
                // All elements in range
                forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 1_000_000_000,
            decreases desc_deltas.len() - j,
        {
            proof {
                Self::lemma_sum_mono(desc_deltas@, (j + 1) as int, desc_deltas.len() as int);
                Self::lemma_sum_nonneg(desc_deltas@, j as int);
            }

            let prev = arr[peak_pos + j];
            let next = prev - desc_deltas[j];

            proof {
                assert(next as int == peak_val as int - Self::sum_deltas(desc_deltas@, (j + 1) as int));

                // next >= 0
                assert(next >= 0) by {
                    Self::lemma_sum_mono(desc_deltas@, (j + 1) as int, desc_deltas.len() as int);
                    assert(Self::sum_deltas(desc_deltas@, (j + 1) as int)
                        <= Self::sum_deltas(desc_deltas@, desc_deltas.len() as int));
                    assert(Self::sum_deltas(desc_deltas@, desc_deltas.len() as int) <= peak_val as int);
                };

                // next < prev (strictly decreasing)
                assert(next < prev) by {
                    assert(desc_deltas[j as int] >= 1);
                };

                // next < all elements in descending part
                assert forall|k: int| peak_pos as int <= k < arr.len() implies arr[k] > next by {
                    let m: int = k - peak_pos as int;
                    assert(0 <= m <= j as int);
                    assert(arr[peak_pos as int + m] as int == peak_val as int - Self::sum_deltas(desc_deltas@, m));
                    assert(arr[k] as int == peak_val as int - Self::sum_deltas(desc_deltas@, m));
                    assert(next as int == peak_val as int - Self::sum_deltas(desc_deltas@, (j + 1) as int));
                    Self::lemma_sum_strict(desc_deltas@, m, (j + 1) as int);
                };
            }

            arr.push(next);
            j = j + 1;

            proof {
                assert forall|k: int, l: int| peak_pos as int <= k < l < arr.len() implies arr[k] > arr[l] by {
                    if l < (arr.len() - 1) as int {
                    } else {
                        assert(arr[l] == next);
                    }
                };
            }
        }

        // Prove is_mountain
        proof {
            assert(arr.len() == total_len);
            assert(total_len >= 3);
            assert(0 < peak_pos < total_len - 1) by {
                assert(peak_pos == asc_deltas.len());
                assert(asc_deltas.len() >= 1);
                assert(desc_deltas.len() >= 1);
            };

            // Ascending: forall a, b with 0 <= a < b <= peak_pos ==> arr[a] < arr[b]
            assert forall|a: int, b: int| 0 <= a < b <= peak_pos as int implies arr@[a] < arr@[b] by {
                assert(arr[a] as int == base as int + Self::sum_deltas(asc_deltas@, a));
                assert(arr[b] as int == base as int + Self::sum_deltas(asc_deltas@, b));
                Self::lemma_sum_strict(asc_deltas@, a, b);
            };

            // Descending: forall a, b with peak_pos <= a < b < len ==> arr[a] > arr[b]
            // Already proved in loop invariant

            assert(Self::is_mountain(arr@, peak_pos as int));
        }

        // Apply mutation to target
        let mutated_target: i32 =
            if mutation_kind == 0 {
                target
            } else if mutation_kind == 1 {
                // target = peak value (guaranteed in array)
                arr[peak_pos]
            } else if mutation_kind == 2 {
                // target = first element
                arr[0]
            } else if mutation_kind == 3 {
                // target = last element
                let last = arr.len() - 1;
                arr[last]
            } else if mutation_kind == 4 {
                // target = 0 (boundary)
                0i32
            } else if mutation_kind == 5 {
                // target = 1_000_000_000 (max boundary)
                1_000_000_000i32
            } else if mutation_kind == 6 && target < 1_000_000_000 {
                // nudge target up
                target + 1
            } else if mutation_kind == 7 && target > 0 {
                // nudge target down
                target - 1
            } else {
                target
            };

        (mutated_target, MountainArray { data: arr })
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn find_in_mountain_array(target: i32, data: &[i32]) -> i32 {
    let n = data.len() as i32;
    let mut left: i32 = 0;
    let mut right: i32 = n - 1;
    while left < right {
        let mid = left + (right - left) / 2;
        if data[mid as usize] < data[(mid + 1) as usize] {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    let peak = left;
    let mut lo: i32 = 0;
    let mut hi: i32 = peak + 1;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if data[mid as usize] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if lo <= peak && data[lo as usize] == target {
        return lo;
    }
    lo = peak + 1;
    hi = n;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if data[mid as usize] > target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if lo < n && data[lo as usize] == target {
        return lo;
    }
    -1
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |data: Vec<i32>, target: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}:{}", data, target);
        if !seen.insert(key) {
            return;
        }
        let result = find_in_mountain_array(target, &data);
        writeln!(out, "{}", json!({
            "input": {"target": target, "mountain_arr": data},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Helper to compute sum of deltas for precondition checks
    fn sum_deltas_val(deltas: &[i32]) -> i64 {
        deltas.iter().map(|&d| d as i64).sum()
    }

    // Helper to build and emit a test case
    fn build_and_emit(
        asc_deltas: Vec<i32>,
        desc_deltas: Vec<i32>,
        base: i32,
        target: i32,
        mutation_kind: u8,
        emit: &mut dyn FnMut(Vec<i32>, i32, &mut HashSet<String>, &mut std::io::BufWriter<std::fs::File>, &mut usize),
        seen: &mut HashSet<String>,
        out: &mut std::io::BufWriter<std::fs::File>,
        emitted: &mut usize,
    ) {
        let (t, ma) = Solution::generate_test_case(&asc_deltas, &desc_deltas, base, target, mutation_kind);
        emit(ma.data, t, seen, out, emitted);
    }

    // Example 1: [1,2,3,4,5,3,1], target = 3
    // asc_deltas = [1,1,1,1] (1->2->3->4->5), desc_deltas = [2,2] (5->3->1), base = 1
    emit(vec![1,2,3,4,5,3,1], 3, &mut seen, &mut out, &mut emitted);

    // Example 2: [0,1,2,4,2,1], target = 3
    emit(vec![0,1,2,4,2,1], 3, &mut seen, &mut out, &mut emitted);

    // Seed cases with all mutation kinds
    let seed_cases: Vec<(Vec<i32>, Vec<i32>, i32, i32)> = vec![
        // (asc_deltas, desc_deltas, base, target)
        (vec![1,1,1,1], vec![2,2], 1, 3),         // example 1
        (vec![1,1,2], vec![2,1], 0, 3),            // example 2
        (vec![1], vec![1], 0, 1),                   // minimal mountain [0,1,0]
        (vec![5], vec![3], 0, 2),                   // [0,5,2]
        (vec![1,1,1], vec![1,1,1], 0, 3),           // symmetric mountain
        (vec![10,10,10], vec![5,5,5], 0, 15),       // larger steps
        (vec![1], vec![1], 100, 101),               // higher base
        (vec![1,2,3], vec![3,2,1], 0, 6),           // different delta sizes
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for (asc, desc, base, target) in &seed_cases {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            build_and_emit(
                asc.clone(), desc.clone(), *base, *target, mk,
                &mut emit, &mut seen, &mut out, &mut emitted,
            );
        }
    }

    // Random test cases with diverse sizes
    while emitted < count {
        // Size class for total array length
        let total_n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(3, 5),        // tiny
            1 => rng.gen_range_usize(3, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // very large
        };

        // Peak position: somewhere between 1 and total_n - 2
        let peak_pos = rng.gen_range_usize(1, total_n - 2);
        let asc_len = peak_pos;
        let desc_len = total_n - 1 - peak_pos;

        // Max delta to keep values <= 1_000_000_000
        let max_total_asc = 1_000_000_000i64;
        let max_delta_asc = std::cmp::max(1, max_total_asc / asc_len as i64);
        let max_delta_asc = std::cmp::min(max_delta_asc, 100_000) as i64;

        let mut asc_deltas: Vec<i32> = Vec::with_capacity(asc_len);
        let mut asc_sum: i64 = 0;
        for _ in 0..asc_len {
            let remaining_slots = asc_len - asc_deltas.len();
            let budget = max_total_asc - asc_sum - remaining_slots as i64;
            let max_d = std::cmp::min(max_delta_asc, std::cmp::max(1, budget));
            let d = rng.gen_range_i64(1, max_d) as i32;
            asc_deltas.push(d);
            asc_sum += d as i64;
        }

        let base = rng.gen_range_i64(0, std::cmp::min(100, 1_000_000_000 - asc_sum)) as i32;
        let peak_val = base as i64 + asc_sum;

        // Descending deltas: sum must be <= peak_val
        let max_desc_sum = peak_val;
        let max_delta_desc = std::cmp::max(1, max_desc_sum / desc_len as i64);
        let max_delta_desc = std::cmp::min(max_delta_desc, 100_000) as i64;

        let mut desc_deltas: Vec<i32> = Vec::with_capacity(desc_len);
        let mut desc_sum: i64 = 0;
        for _ in 0..desc_len {
            let remaining_slots = desc_len - desc_deltas.len();
            let budget = max_desc_sum - desc_sum - remaining_slots as i64;
            let max_d = std::cmp::min(max_delta_desc, std::cmp::max(1, budget));
            let d = rng.gen_range_i64(1, max_d) as i32;
            desc_deltas.push(d);
            desc_sum += d as i64;
        }

        // Target: mix of boundary and random values
        let target = match rng.gen_range_usize(0, 4) {
            0 => 0i32,
            1 => rng.gen_range_i64(0, peak_val.min(1_000_000_000)) as i32,
            2 => peak_val.min(1_000_000_000) as i32,
            3 => rng.gen_range_i64(0, 1_000_000_000) as i32,
            _ => base,
        };

        let mk = rng.gen_range_usize(0, 8) as u8;

        build_and_emit(
            asc_deltas, desc_deltas, base, target, mk,
            &mut emit, &mut seen, &mut out, &mut emitted,
        );
    }

    eprintln!("Generated {} test cases", emitted);
}
