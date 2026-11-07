# K-th Smallest Prime Fraction

You are given a sorted integer array `arr` containing `1` and prime numbers, where all the integers of `arr` are unique. You are also given an integer `k`.

For every `i` and `j` where `0 <= i < j < arr.length`, we consider the fraction `arr[i] / arr[j]`.

Return the `k`-th smallest fraction considered. Return your answer as an array of two integers, where `answer[0] == arr[i]` and `answer[1] == arr[j]`.

## Example 1

> **Input:** arr = [1,2,3,5], k = 3  
> **Output:** [2,5]  
> **Explanation:** The fractions in sorted order are: 1/5, 1/3, 2/5, 1/2, 3/5, 2/3. The third is 2/5.

## Example 2

> **Input:** arr = [1,7], k = 1  
> **Output:** [1,7]

## Constraints

- `2 <= arr.length <= 1000`
- `1 <= arr[i] <= 3 * 10^4`
- `arr[0] == 1`
- `arr[i]` is prime for `i > 0`
- All elements are unique and sorted in strictly increasing order
- `1 <= k <= arr.length * (arr.length - 1) / 2`

## Starter Code

```dafny
predicate kth_smallest_prime_fraction_pre(arr: seq<int>, k: int)

predicate kth_smallest_prime_fraction_post(arr: seq<int>, k: int, result: seq<int>)
  requires kth_smallest_prime_fraction_pre(arr, k)

method kth_smallest_prime_fraction(arr: seq<int>, k: int) returns (result: seq<int>)
  requires kth_smallest_prime_fraction_pre(arr, k)
  ensures kth_smallest_prime_fraction_post(arr, k, result)
```
