# Valid Anagram

Given two strings `s` and `t`, return `true` if `t` is an anagram of `s`, and `false` otherwise.

## Example 1:

> **Input:** s = "anagram", t = "nagaram"
> **Output:** true

## Example 2:

> **Input:** s = "rat", t = "car"
> **Output:** false

## Constraints:

- $1 \leq \texttt{s.length}, \texttt{t.length} \leq 5 \times 10^4$
- `s` and `t` consist of lowercase English letters.

## Starter Code

```dafny
predicate is_anagram_pre(s: string, t: string)

predicate is_anagram_post(s: string, t: string, res: bool)
  requires is_anagram_pre(s, t)

method is_anagram(s: string, t: string) returns (res: bool)
  requires is_anagram_pre(s, t)
  ensures is_anagram_post(s, t, res)
```
