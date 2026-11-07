# Check If All 1's Are at Least Length K Places Away

Given a binary array `nums` and an integer `k`, return `true` if all `1`'s are at least `k` places away from each other, and `false` otherwise.

## Example 1:

> **Input:** nums = [1,0,0,0,1,0,0,1], k = 2
> **Output:** true
> **Explanation:** Each of the `1`'s is at least 2 places away from the next `1`.

## Example 2:

> **Input:** nums = [1,0,0,1,0,1], k = 2
> **Output:** false
> **Explanation:** The second `1` and third `1` are only one place apart.

## Constraints:

- `1 <= nums.length <= 10^5`
- `0 <= k <= nums.length`
- `nums[i]` is either `0` or `1`

## Starter Code

```dafny
predicate k_length_apart_pre(nums: seq<int>, k: int)

predicate k_length_apart_post(nums: seq<int>, k: int, result: bool)
  requires k_length_apart_pre(nums, k)

method k_length_apart(nums: seq<int>, k: int) returns (result: bool)
  requires k_length_apart_pre(nums, k)
  ensures k_length_apart_post(nums, k, result)
```
