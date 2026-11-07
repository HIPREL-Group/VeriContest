680. Valid Palindrome II

Given a string `s`, return `true` if the `s` can be palindrome after deleting at most one character from it.

## Example 1

Input: `s = "aba"`
Output: `true`

## Example 2

Input: `s = "abca"`
Output: `true`
Explanation: You could delete the character `'c'`.

## Example 3

Input: `s = "abc"`
Output: `false`

## Constraints

- `1 <= s.length <= 10^5`
- `s` consists of lowercase English letters.

## Starter Code

```dafny
predicate valid_palindrome_pre(s: seq<char>)

predicate valid_palindrome_post(s: seq<char>, res: bool)
  requires valid_palindrome_pre(s)

method valid_palindrome(s: seq<char>) returns (res: bool)
  requires valid_palindrome_pre(s)
  ensures valid_palindrome_post(s, res)
```
